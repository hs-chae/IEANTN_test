#!/usr/bin/env python3
"""Directed numerical cross-check of independently derived box-proof anchors.

These native Arb calculations are review evidence, not source-first PV, a Lean
proof, or exhaustive sampling. The all-L conclusions use the explicitly recorded
analytic monotonicity and elementary comparison arguments in REVIEW.json.
"""
from pathlib import Path
import argparse,hashlib,json,sys,time
from flint import arb,ctx
ctx.prec=256
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
if a.out.exists():raise ValueError('fresh output required')
start=time.monotonic();q=lambda s:arb(str(s));pi=arb.pi();L=q(35);A=q(12)
delta=L/(2*pi*(L/2).exp());v=L/2-L.log();z=(A/(2*pi)).log()
main=A/(2*pi)*(z-1)+q(7)/8
constant=2*main/A+q('.56')*(A.log()+1)/A-z*z/(2*pi)
H0=q(31)/24
H1=(2*q(2).log()-1)/3+(q(2).log()+1)/2+(q(2).log()/2+q(1)/4)/4
derivative=q('.56')*delta*((-delta.log())*q('1.3')+q('1.2'))
T=3/delta;w=(T/(2*pi)).log()
clip=w*w/(2*pi)+q('.131')+(w+1)/pi+(q('1.12')*T.log()+q('.28'))/T
small=(A*delta)**2/(6*pi)*(q(1)/4+z/2)
checks=[]
def row(name,value,bound):
 if not value<q(bound):raise ArithmeticError('not strictly enclosed: '+name)
 checks.append({'id':name,'enclosure':str(value),'strict_upper':str(bound)})
row('N12_upper',main+q('.28')*A.log(),'1')
row('density_constant',constant,'.130')
row('delta35',delta,'1.4e-7')
row('L2delta35',L*L*delta,'.000172')
row('H0',H0,'1.3');row('H1',H1,'1.2')
row('density_derivative35',derivative,'.000003')
row('small_y_regularization35',small,'1e-10')
row('clipped_sum35',clip,'61.25')
row('whole_ray_clip_ratio_coarse',q(1)/24+q(1)/(6*35)+(q(1)/3+q('.132'))/(35*35),'.05')
row('tail_remainder_at_1e7',(q('1.12')*q('1e7').log()+q('.28'))/q('1e7'),'.000002')
row('moment_to_B5_gain35',((q('1.662')-2*q(2).log())*v+q('1.148')-q('1.4175'))/(2*pi),'.6')
# The previous row is only an upper cross-check; the actual needed lower gate:
gain=((q('1.662')-2*q(2).log())*v+q('1.148')-q('1.4175'))/(2*pi)
if not gain>q('.546'):raise ArithmeticError('B5 lower gain anchor failed')
checks.append({'id':'B5_gain35_lower','enclosure':str(gain),'strict_lower':'.546'})
r={'schema':'INDEPENDENT_BOX_SCALAR_REVIEW_V1','status':'PASS','source_first_PV':False,'kernel_proof':False,'precision_bits':ctx.prec,'python':sys.version,'python_optimization':sys.flags.optimize,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'checks':checks,'elapsed_seconds':time.monotonic()-start}
a.out.parent.mkdir(parents=True,exist_ok=True);tmp=a.out.with_name(a.out.name+'.tmp');tmp.write_text(json.dumps(r,indent=2)+'\n');tmp.replace(a.out);print('PASS',len(checks),'directed anchor checks')
