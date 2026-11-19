#!/usr/bin/python3.10
"""Ancillary reproduction using the candidate's unchanged arithmetic and parameters."""
from verify import *
from d02 import *
n=38358837682;x=I(n)+I('.1')
R=exp0(1)*x*632207037/log(x)-1644673232**2
assert R.below(-7900000)
print('Printed PT real early reading counterexample, x=n+.1, R=',R.fmt())
x=I('1.0000001'); t=log(x); sx=expb(t/2)
T=2*piB**2*sx/t
assert T.above(10**7) and T.below(3000175332800)
assert (sx*t**2/(8*piB)).below('1e-14')
print('CH2 Cor. 9.3 literal near-one counterexample, x=1.0000001, T=',T.fmt())
assert (1/(1-I(2)/58)).below('1.04')
assert (115/(I('.5')-I(2)/58)).below(248)
assert (1/(I('.875')-I(2)/200)).below('1.16')
assert (1/(1-I(2)/21)).below('1.11')
assert (1/(I('.5')-I(2)/21)).below('2.48')
assert (I('1.000000147')+I('1.78')*exp0(F(-21,6))).below('1.06')
assert (I('113.67')+I('1.000000147')+I('1.78')*exp0(F(-58,6))).below(115)
assert (I(2)/3-I(4)/40-I(3)*2/25-4*I(41)/(40*26)-I('.001')).above('.166')
assert (1/(1-2*I(42)/(27*40))).below('1.1')
assert (3*exp0(-F(845,32))).below(1)
print('Analytic constants and all-order worst endpoints verified')
ns=[];vals=[]
for s in open('sieve-results.txt'):
 if s.startswith('bin'):
  n=int(s.split('[')[1].split(',')[0]); vals.append(list(map(int,s.split(': ')[1].split())));ns.append(n)
for n,p,w in [(2500000,'.20','.213'),(4000000,'.161','.172'),(20000000,'.090','.096'),(50000000,'.057','.062'),(100000000,'.057','.060')]:
 s,ww,z=map(max,zip(*vals[ns.index(n):]))
 c=I(z)/10000
 assert (I(s)/10000).below(p) and (I(ww)/10000).below(w)
 assert (c/(1-c/log(n)**3)).below(p)
assert (I('.0096')/(1-I('.0096')/log(9750000000)**3)).below('.0100')
print('Finite suffix coefficients and newest .0503 bridge checked')
from verify import low_res,cellerr, tail as oldtail,poly
a,b,cs,k='190','190.1',[1,14],1
e=low_res(F(a),F(b),cs,k)-cellerr(F(a),F(b),k)-0
assert e.below(0);print('Failed sufficient cell',a,b,cs,e.fmt())
try: oldtail(700,[poly[j] for j in range(19)],19)
except AssertionError as e:print('Failed sufficient old tail at 700:',e)
else:raise AssertionError('unexpected old certificate success')
from early import cell
for a,c in [('36.52',0),('39.666','.30')]:
 r=cell(F(a),F(a),c)
 assert r.below(0);print('Failed sufficient early endpoint',a,c,r.fmt())
z=mcap(F(1240),B2,False)
assert z.above('.160');print('Failed sufficient .160 power cap at 1240',z.fmt())
assert (F(3,5)*exp0(F(1,2))).below(1)

