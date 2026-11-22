#!/usr/bin/env python3
from pathlib import Path
import argparse,json,time,sys,hashlib
from rational import F,I,PI,log,exp,need
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);a=p.parse_args();need(not a.out.exists(),'fresh output');rows=[]
def check(name,left,right,direction):
    need(left.lt(right)if direction=='<'else left.gt(right),name)
    rows.append({'name':name,'left':left.row(),'relation':direction,'right':str(right)})
L=I(24);d=F(109,100)*L-1;cap=F(109,100)*24*exp(-12)
check('delta cap',cap,F(1,6000),'<')
check('positive log coefficient',log(1/(2*PI*d*exp(-12))),0,'>')
V=I(F(50,9))+sum(F(c,(k-1)*5**(k-1))for k,c in[(2,12),(3,84),(4,420),(5,1680),(6,5040),(7,10080),(8,10080)])
Vlog=F(4,9)*(F(25,2)*log(5)-6)+sum(F(c,(k-1)*5**(k-1))*(log(5)+F(1,k-1))for k,c in[(2,12),(3,84),(4,420),(5,1680),(6,5040),(7,10080),(8,10080)])
W=F(12,7)*log(5)+sum(F(c,k*5**k)for k,c in[(2,12),(3,60),(4,240),(5,720),(6,1440),(7,1440)])
check('total variation',V,'12','<');check('log variation',Vlog,23,'<');check('weighted tail',W,'4','<')
R=2*cap*(F(3,2)+F(12)*(1+F('.28')*log(1/cap))+F('.28')*23)
check('zero discrepancy',R,'.017','<')
Q=F('1.0002')*F('1.001')*L*exp(-12)*(F('4.0008')*L+log(2*L))
check('nonprime powers',Q,'.0155','<')
check('count log margin',F('1.72')*log(2*PI*d)-(F(12,7)+F('1.3')+F('.034')),'5.6','>')
check('whole-ray width control',F('8.72')*24*cap,'.04','<')
check('trivial-zero remainder',2*cap/(exp(F(23,2))*(exp(46)-1)),'.001','<')
# The monotonicity signs needed in the written full-domain extension.
check('D positive',d,0,'>');check('log slope positive',I(F(1,2))-F(109,100)/d,0,'>')
check('delta slope negative at left',I(F(109,100))-d/2,0,'<')
check('Q polynomial-log decay condition',I(2)/L+1/(L*log(2*L)),F(1,2),'<')
check('width error decay condition',I(2)/L,F(1,2),'<')
record={'schema':'SEXTIC_WHOLE_RAY_SCALAR_ENDPOINTS_V1','status':'PASS','checks':rows,'python_optimization':sys.flags.optimize,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'mathematical_domain':'L>=24; explicit monotonicity derivations in SEXTIC_PROOF.md','numeric_samples_are_not_domain_proof':True};a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(record,indent=2)+'\n');print(json.dumps({'status':'PASS','checks':len(rows),'mode':sys.flags.optimize}))
