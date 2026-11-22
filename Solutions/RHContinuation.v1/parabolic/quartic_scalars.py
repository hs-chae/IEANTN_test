#!/usr/bin/env python3
from pathlib import Path
import argparse,json,time,sys,hashlib
from rational import F,I,PI,log,exp,need
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);a=p.parse_args();need(not a.out.exists(),'fresh output');rows=[]
def check(name,left,right,direction):
    need(left.lt(right)if direction=='<'else left.gt(right),name)
    rows.append({'name':name,'left':left.row(),'relation':direction,'right':str(right)})
L=I(24);d=F(111,100)*L-1;cap=F(111,100)*24*exp(-12)
check('delta cap',cap,F(1,6000),'<')
check('positive log coefficient',log(1/(2*PI*d*exp(-12))),0,'>')
V=I(F(64,21))+sum(F(c,(k-1)*4**(k-1))for k,c in[(2,8),(3,40),(4,120),(5,240),(6,240)])
Vlog=F(8,21)*(8*log(4)-F(15,4))+sum(F(c,(k-1)*4**(k-1))*(log(4)+F(1,k-1))for k,c in[(2,8),(3,40),(4,120),(5,240),(6,240)])
W=F(8,5)*log(4)+sum(F(c,k*4**k)for k,c in[(2,8),(3,24),(4,48),(5,48)])
check('total variation',V,'7.21','<');check('log variation',Vlog,12,'<');check('weighted tail',W,'2.7','<')
R=2*cap*(F(7,5)+F('7.21')*(1+F('.28')*log(1/cap))+F('.28')*12)
check('zero discrepancy',R,'.011','<')
Q=F('1.0002')*F('1.001')*L*exp(-12)*(F('4.0008')*L+log(2*L))
check('nonprime powers',Q,'.0155','<')
check('count log margin',F('1.54')*log(2*PI*d)-F('2.528'),'5.2','>')
check('whole-ray width control',F('8.88')*24*cap,'.04','<')
check('trivial-zero remainder',2*cap/(exp(F(23,2))*(exp(46)-1)),'.001','<')
# The monotonicity signs needed in the written full-domain extension.
check('D positive',d,0,'>');check('log slope positive',I(F(1,2))-F(111,100)/d,0,'>')
check('delta slope negative at left',I(F(111,100))-d/2,0,'<')
check('Q polynomial-log decay condition',I(2)/L+1/(L*log(2*L)),F(1,2),'<')
check('width error decay condition',I(2)/L,F(1,2),'<')
record={'schema':'QUARTIC_WHOLE_RAY_SCALAR_ENDPOINTS_V1','status':'PASS','checks':rows,'python_optimization':sys.flags.optimize,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'mathematical_domain':'L>=24; explicit monotonicity derivations in QUARTIC_PROOF.md','numeric_samples_are_not_domain_proof':True};a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(record,indent=2)+'\n');print(json.dumps({'status':'PASS','checks':len(rows),'mode':sys.flags.optimize}))
