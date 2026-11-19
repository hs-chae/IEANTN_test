#!/usr/bin/python3.10
from pathlib import Path
import anchor
from cert import I,Q,D

# Same directed bridge and same grid, parameterized here by generated source.
p=Path(anchor.__file__)
s=p.read_text()
assert s.count("D('.0223')")==2
ns={'__file__':str(p),'__name__':'bridge14'}
exec(compile(s.replace("D('.0223')","D('.02214')"),str(p),'exec'),ns)
ns['chk']()
# From 200 onward compare using B0 M0 with coefficient .01880.
assert (I('.01880')*200**2*(-I(25)).exp()).b<D('.02214')
