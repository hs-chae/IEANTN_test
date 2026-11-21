#!/usr/bin/python3.10
"""Tight rational bracket for the crossing (scalar check, not C-source PV)."""
from ram_cert import Q, expi, logi, req
E0,E1=expi(Q(1))
P=1644673232
M=632207037
A=Q(38358837682)
B=A+1
ilo=Q("38358837682.21792636514465772878")
ihi=Q("38358837682.21792636514465772879")
l1,l2=logi(ilo)
h1,h2=logi(ihi)
req(0<l1<l2 and 0<h1<h2)
m0=E1*ilo*M-P**2*l1
m1=E0*ihi*M-P**2*h2
req(A<ilo<ihi<B)
req(m0<0<m1)
print("unique crossing bracket:", ilo, ihi)
print("rational upper/lower sign margins for G(x)*log(x):",
      float(m0),float(m1))
