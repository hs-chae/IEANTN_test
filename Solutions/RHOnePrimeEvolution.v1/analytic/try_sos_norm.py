#!/usr/bin/env python3
"""Bounded exploratory SDP for SOS majorants of a fixed Gaussian polynomial.
Solver output is explicitly unverified; no PSD/rounding/Lean claim is made.
"""
from pathlib import Path
import argparse,json,time,resource,hashlib
import sympy as s,numpy as np,cvxpy as cp
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--candidate',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--basis-degree',type=int,required=True);p.add_argument('--solver',default='CLARABEL');a=p.parse_args()
if a.out.exists():raise SystemExit('fresh output required')
a.out.mkdir(parents=True);tt=time.monotonic();v=s.Symbol('v');src=json.loads(a.candidate.read_text());cs=[s.Rational(x)for x in src['coefficients_decimal_exact_rationals']];P=s.Poly(sum(c*s.assoc_laguerre(k,s.Rational(-1,2),2*v)for k,c in enumerate(cs)),v);d=a.basis_degree;N=2*d+1
if P.degree()>2*d:raise ValueError('basis degree too small')
# Exact rational change of basis, converted only AFTER algebraic construction.
Lb=[s.Poly(s.assoc_laguerre(k,s.Rational(-1,2),v),v)for k in range(N)]
M=s.Matrix(N,N,lambda i,j:Lb[j].nth(i));MInv=M.inv();Sbasis=Lb[:d+1];Tbasis=[s.Poly(s.assoc_laguerre(k,s.Rational(1,2),v),v)for k in range(d)]
def product_map(basis,shift):
 n=len(basis);out=np.zeros((N,n,n))
 for i in range(n):
  for j in range(i,n):
   pr=basis[i]*basis[j]*s.Poly(v**shift,v);vec=MInv*s.Matrix([pr.nth(k)for k in range(N)])
   fs=np.array([float(z)for z in vec]);out[:,i,j]=fs;out[:,j,i]=fs
 return out
MS=product_map(Sbasis,0);MT=product_map(Tbasis,1);target=np.array([float(z)for z in MInv*s.Matrix([P.nth(k)for k in range(N)])]);weightsS=np.array([float(s.binomial(2*k,k)/4**k)for k in range(d+1)]);weightsT=np.array([float((2*k+1)*s.binomial(2*k,k)/(2*4**k))for k in range(d)])
Splus=cp.Variable((d+1,d+1),symmetric=True);Sminus=cp.Variable((d+1,d+1),symmetric=True);Tplus=cp.Variable((d,d),symmetric=True);Tminus=cp.Variable((d,d),symmetric=True)
constraints=[Splus>>0,Sminus>>0,Tplus>>0,Tminus>>0]
for k in range(N):constraints.append(cp.sum(cp.multiply(MS[k],Splus-Sminus))+cp.sum(cp.multiply(MT[k],Tplus-Tminus))==2*target[k])
objective=(weightsS@(cp.diag(Splus)+cp.diag(Sminus))+weightsT@(cp.diag(Tplus)+cp.diag(Tminus)))/2;prob=cp.Problem(cp.Minimize(objective),constraints)
setup=time.monotonic()-tt
try:
 if a.solver=='CLARABEL':prob.solve(solver=a.solver,max_iter=200,tol_gap_abs=1e-8,tol_feas=1e-8,verbose=False)
 else:prob.solve(solver=a.solver,max_iters=10000,eps=1e-7,verbose=False)
except Exception as e:
 (a.out/'FAILURE.json').write_text(json.dumps({'status':'SDP_SOLVER_FAILURE_NOT_A_MATHEMATICAL_COUNTEREXAMPLE','error':str(e),'setup_seconds':setup,'elapsed_seconds':time.monotonic()-tt,'basis_degree':d,'solver':a.solver,'target_coefficient_max':float(np.max(np.abs(target))),'S_map_max':float(np.max(np.abs(MS))),'T_map_max':float(np.max(np.abs(MT)))},indent=2)+'\n');raise
rec={'status':'EXPLORATORY_SDP_NOT_A_CERTIFICATE','solver_status':prob.status,'objective_L1_majorant_heuristic':prob.value,'candidate':str(a.candidate),'candidate_sha256':hashlib.sha256(a.candidate.read_bytes()).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'basis_degree':d,'setup_seconds':setup,'seconds':time.monotonic()-tt,'solver':a.solver,'cvxpy':cp.__version__,'solver_stats':{'iterations':prob.solver_stats.num_iters,'solve_time':prob.solver_stats.solve_time},'peak_RSS_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
for name,X in [('Splus',Splus),('Sminus',Sminus),('Tplus',Tplus),('Tminus',Tminus)]:
 if X.value is not None:rec[name]=X.value.tolist();rec[name+'_min_eigenvalue']=float(np.linalg.eigvalsh(X.value)[0])
if Splus.value is not None and Sminus.value is not None and Tplus.value is not None and Tminus.value is not None:
 residual=np.einsum('kij,ij->k',MS,Splus.value-Sminus.value)+np.einsum('kij,ij->k',MT,Tplus.value-Tminus.value)-2*target
 rec['max_exact_constraint_float_residual']=float(np.max(np.abs(residual)))
(a.out/'RESULT.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps({k:v for k,v in rec.items()if k not in ['Splus','Sminus','Tplus','Tminus']}))
