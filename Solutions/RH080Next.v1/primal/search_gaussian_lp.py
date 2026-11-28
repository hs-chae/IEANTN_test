#!/usr/bin/env python3
"""Finite-grid Gaussian LP exploration, followed by continuous sign-root review.

Not a certificate, Lean theorem, source-first PV, or global optimality claim.
"""
import argparse,hashlib,json,math,sys,time,warnings
from pathlib import Path
import numpy as np
import scipy
from scipy import optimize,sparse
from search_gaussian import hm,vals0,exact_objective,candidate,A,SQ,need

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--degree',type=int,required=True);ap.add_argument('--scale',type=float,default=1.);ap.add_argument('--dx',type=float,default=.004);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--threads',type=int,default=2);a=ap.parse_args()
    need(not a.out.exists(),'Fresh output directory');a.out.mkdir(parents=True);start=time.monotonic();n=a.degree;s=a.scale
    source=a.out/'source';source.mkdir();source_hashes={}
    for name in ['search_gaussian.py','search_gaussian_lp.py']:
        p=Path(__file__).with_name(name);raw=p.read_bytes();(source/name).write_bytes(raw);source_hashes[name]=hashlib.sha256(raw).hexdigest()
    end=max(14.,math.sqrt(4*n)+5);points=[];matrices=[];weights=[]
    for low in [0.,SQ/s]:
        count=math.ceil((end-low)/a.dx);dx=(end-low)/count;x=low+dx*(np.arange(count)+.5);b=hm(x,n)
        keep=np.max(abs(b),axis=1)>1e-16;x=x[keep];b=b[keep]
        points.append(x);matrices.append(b);weights.append(np.full(len(x),2*dx/SQ))
    B,G=matrices;G=G*((-1.)**np.arange(n+1));N,M=len(B),len(G)
    bc=sparse.csr_matrix(B);gc=sparse.csr_matrix(G);zNM=sparse.csr_matrix((N,M));zMN=sparse.csr_matrix((M,N));identityN=sparse.eye(N,format='csr');identityM=sparse.eye(M,format='csr')
    Aub=sparse.vstack([sparse.hstack([bc,-identityN,zNM]),sparse.hstack([-bc,-identityN,zNM]),sparse.hstack([gc,zMN,-identityM])],format='csr');bub=np.zeros(2*N+M)
    Aeq=sparse.csr_matrix(np.r_[vals0(n),np.zeros(N+M)][None,:]);bounds=[(None,None)]*(n+1)+[(0,None)]*(N+M)
    r=.83394544;history=[]
    for it in range(3):
        cost=np.r_[np.zeros(n+1),weights[0]/s,r*A*weights[1]]
        with warnings.catch_warnings(record=True)as captured:
            p=optimize.linprog(cost,A_ub=Aub,b_ub=bub,A_eq=Aeq,b_eq=[1.],bounds=bounds,method='highs-ipm',options={'primal_feasibility_tolerance':1e-9,'dual_feasibility_tolerance':1e-9,'ipm_optimality_tolerance':1e-11,'threads':a.threads,'random_seed':0})
        need(p.success,'LP failed: '+p.message);c=p.x[:n+1];free=c[1:]/(vals0(n)@c)
        value,grad,H,data,roots,_=exact_objective(free,s,r);q=data['N']/(1-A*data['J'])
        history.append(dict(iteration=it,r=r,LPobjective=float(p.fun),continuous_ratio=q,data=data,max_gradient=float(max(abs(grad))),solver=p.message,LPiterations=p.nit,warnings=[str(w.message)for w in captured]))
        print(json.dumps(dict(degree=n,scale=s,dx=a.dx,**history[-1])),flush=True)
        r=q
    packet=candidate(free);packet.update(scale=s,searched_ratio=q,grid_dx=a.dx)
    (a.out/'CANDIDATE.json').write_text(json.dumps(packet,indent=2)+'\n');(a.out/'HERMITE.json').write_text(json.dumps(list(map(float,c))))
    for name,h in source_hashes.items():need(hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()==h,'Search source changed during run')
    result=dict(status='FLOATING_GRID_LP_WITH_CONTINUOUS_ROOT_REVIEW_NOT_A_CERTIFICATE',degree=n,physical_degree=2*n,scale=s,ratio=q,data=data,roots=roots,history=history,grid={'dx':a.dx,'cutoff':end,'norm_samples':N,'wing_samples':M},seconds=time.monotonic()-start,seed=0,python=sys.version,numpy=np.__version__,scipy=scipy.__version__,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),source_hashes=source_hashes)
    (a.out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k]for k in ['status','degree','scale','ratio','seconds']}),flush=True)
if __name__=='__main__':main()
