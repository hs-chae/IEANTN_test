#!/usr/bin/env python3
from pathlib import Path
import argparse,json,hashlib,sys
from rational import I,F,PI,log,exp,need
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);a=p.parse_args();need(not a.out.exists(),'fresh output');rows=[]
def c(name,left,right,way):
 need(left.lt(right)if way=='<'else left.gt(right),name);rows.append({'name':name,'left':left.row(),'relation':way,'right':str(right)})
L=I(35);de=L/(2*PI*exp(L/2));v=L/2-log(L);q=log(12/(2*PI));M=I(12)/(2*PI)*(q-1)+F(7,8)
c('delta',de,'.00000015','<');c('deltaL2',de*L**2,'.00018','<');c('v left',v,'13.5','>')
C=M/6+F('.56')*(log(12)+1)/12-q**2/(2*PI);c('zero boundary constant',C,'.130','<')
H0=I(F(2,3))+F(1,2)+F(1,8)
H1=(2*log(2)-1)/3+(log(2)+1)/2+(log(2)+F(1,2))/8
c('H0',H0,'1.3','<');c('H1',H1,'1.2','<')
c('derivative discrepancy',F('.56')*de*(F('1.3')*log(1/de)+F('1.2')),'.000003','<')
c('imaginary shift',de*L**2/4*exp(de/2),'.000046','<')
c('external shift',(exp(de/2)-1)*L**2,'.000181','<')
c('main normalized excess',L/(2*PI)*(exp(2*de)-1),'.001','<')
c('trivial normalized',F('1.9')*exp(-L/2),'.001','<')
c('uniform B5 improvement', (F('.26')*v-F('.352'))/(2*PI),'.5','>')
# Clippedsum heightT=3/delta, lowerendpoint andsubleading tail.
T=3/de;s=log(T/(2*PI));tail=(F('1.12')*log(T)+F('.28'))/T
c('clippedsum anchor',s**2/(2*PI)+F('.131')+(s+1)/PI+tail,L.l**2,'<')
c('removed nearzero regularization',(12*de)**2/PI*(F(1,24)+q/12),'.0000000001','<')
record={'schema':'BOX_POINTWISE_WHOLE_RAY_SCALAR_GATES_V1','status':'PASS','checks':rows,'python_optimization':sys.flags.optimize,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'domain_extension':'Written monotonicity and coarse L² majorants in BOX_PNT_PROOF.md; point checks alone are not the ray proof'};a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(record,indent=2)+'\n');print(json.dumps({'status':'PASS','checks':len(rows),'mode':sys.flags.optimize}))
