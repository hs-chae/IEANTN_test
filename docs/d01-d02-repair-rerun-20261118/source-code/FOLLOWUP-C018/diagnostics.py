#!/usr/bin/python3.10
"""Negative tests for particular formulas, not claimed counterexamples to R."""
from certify import *
for L,idx,k,d in [('150',0,2,'0'),('150',1,2,'0'),('185',1,2,'0'),
                  ('186',0,2,'0'),('200',0,2,'0'),('210',1,3,'0'),
                  ('186',0,1,'39'),('165',1,1,'144')]:
 u=D(L)
 v=gap(u,u,idx,k)-I(d)/I(u)**(k+1)
 assert v.b<0,(L,idx,k,d,v)
 print('Proof formula cannot certify requested margin at',L,idx,k,d,v)
