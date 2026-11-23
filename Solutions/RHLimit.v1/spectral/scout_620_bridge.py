#!/usr/bin/env python3
"""Deterministic exact-rational discovery only; Lean independently checks leaves."""
from pathlib import Path
import json
from refined_ram_p8_p1_16 import Q,p,q,lo,hi,lower_powers,upper_powers,coef,down
D=10**12
def floorq(x): return Q(x.numerator*D//x.denominator,D)
def ceilq(x): return -floorq(-x)
def shift(l,u): return Q('.1386')/(l-6)+Q('14.44')*u*hi(-l/2)
def run():
 ends=[Q(444873,16384),Q(55611,2048),Q(111237,4096),Q(27813,1024),Q(6957,256),Q(1743,64)]
 rows=[]
 for l,u in zip(ends,ends[1:]):
  c=floorq(-Q('.88')-shift(l,u)+lower_powers(l,u));d=ceilq(Q('.68')+shift(l-1,u-1)+upper_powers(l-1))
  B=sum(coef[j]/u**(j-4) for j in range(4,21))-Q('.001')
  margin=down(B-d*l**5/(l-1)*hi((1-l)/2)+2*p(20,u)*c*u**4*lo(-u/2)-c*c*l**4*hi(-l))
  if not margin>Q('.001'):raise ValueError((l,u,float(margin)))
  row={k:str(v)for k,v in dict(l=l,u=u,c=c,d=d,margin=margin).items()};rows.append(row)
 return {'schema':'RAM620_DISCOVERY_ONLY','source_first_PV':False,'native_or_kernel_acceptance':False,'onset':'620000000000','target_margin':'1/1000','rows':rows}
if __name__=='__main__':
 print(json.dumps(run(),indent=2))
