import json,sys
from fractions import Fraction as Q
from math import sqrt
from pathlib import Path
from gauss_cert import lag
for path in sys.argv[1:]:
 d=json.load(open(path)); prod=1.; w=[Q(0)]
 for i,x in enumerate(d['x'],1):
    prod*=(i-.5)/i
    w.append(Q(round(10**20*x/sqrt(prod)),10**20))
 w[0]=1-sum(lag(i)[0]*x for i,x in enumerate(w[1:],1))
 A='36/11' if d['A']>3 and d['A']<3.5 else str(d['A'])
 Path(path[:-5]+'_rat.json').write_text(json.dumps({'A':A,'laguerre':list(map(str,w))},indent=2)+'\n')
