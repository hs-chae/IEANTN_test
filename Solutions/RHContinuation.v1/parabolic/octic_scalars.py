#!/usr/bin/env python3
"""Exact endpoint gates for octic full-ray and full-C-family written proofs."""
from pathlib import Path
import argparse,json,hashlib,sys
from rational import F,I,PI,log,exp,need
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);a=p.parse_args();need(not a.out.exists(),'fresh output');rows=[]
def ck(name,left,right,way):
 need(left.lt(right)if way=='<'else left.gt(right),name);rows.append({'name':name,'left':left.row(),'relation':way,'right':str(right)})
Dco=[(2,16),(3,144),(4,1008),(5,6048),(6,30240),(7,120960),(8,362880),(9,725760),(10,725760)]
Fco=[(2,16),(3,112),(4,672),(5,3360),(6,13440),(7,40320),(8,80640),(9,80640)]
V=I(F(96,11))+sum(F(c,(k-1)*6**(k-1))for k,c in Dco)
Vlog=F(16,33)*(18*log(6)-F(35,4))+sum(F(c,(k-1)*6**(k-1))*(log(6)+F(1,k-1))for k,c in Dco)
W=F(16,9)*log(6)+sum(F(c,k*6**k)for k,c in Fco)
ck('octic variation',V,18,'<');ck('octic logvariation',Vlog,34,'<');ck('octic weighted variation',W,4,'<')
L=I(24);m=F(16,9);A=F('1.822');B=F('1.5');C=F('2.15');D=C*L/2-1;cap=C*24/2*exp(-12)
ck('specific delta cap',cap,F(1,6000),'<')
R=2*cap*(F(14,9)+18*(1+F('.28')*log(1/cap))+F('.28')*34)
ck('specific zero discrepancy',R,'.024','<')
ck('specific full log margin',A*log(2*PI*D)-m-B-F('.041'),'5.8','>')
ck('specific width correction',4*C*L*cap,2,'<')
ck('specific count excess',I(m*C/2-A/2),1,'>')
need(m*C/2-A/2==F(9001,9000),'exact lambda identity')
# Full C range[1.03,16]. Every endpoint reduction is monotone in the
# stated C/L domain; see OCTIC_PROOF.md rather than treating samples asproof.
Cmin=F('1.03');Cmax=16;Dmin=Cmin*L/2-1;capmax=8*24*exp(-12)
ck('family delta cap',capmax,F(1,800),'<')
Rmax=2*capmax*(F(14,9)+18*(1+F('.28')*log(1/capmax))+F('.28')*34)
ck('family zero discrepancy',Rmax,'.15','<')
ck('family expfactor',exp(capmax/2),'1.0006','<')
Qmax=F('1.0006')*F('1.001')*L*exp(-12)*(F('16.0096')*L+log(2*L))
ck('family primepower cost',Qmax,'.058','<')
ck('family log margin',A*log(2*PI*Dmin)-m-B-F('.21'),'4.2','>')
ck('family width control',4*Cmax*L*capmax,2,'<')
ck('family countcoefficient positive',I(m*Cmin/2-A/2),0,'>')
ck('family log coefficient positive',log(1/(2*PI*capmax)),0,'>')
ck('family trivial tail',2*capmax/(exp(F(23,2))*(exp(46)-1)),'.001','<')
ck('family K<2L', (L+capmax)/log(2),48,'<')
# Positive polynomial/exponential factors decrease throughoutL>=24.
ck('L² exp decay',I(2)/L,F(1,2),'<')
ck('Llog(2L)exp decay',I(1)/L+1/(L*log(2*L)),F(1,2),'<')
record={'schema':'OCTIC_FULL_RAY_AND_PARAMETER_FAMILY_SCALARS_V1','status':'PASS','checks':rows,'python_optimization':sys.flags.optimize,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'mathematical_domain':'L>=24, C=2.15 or C in[1.03,16]; analytic monotonicity and width proof inOCTIC_PROOF.md','numeric_samples_are_not_domain_proof':True};a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(record,indent=2)+'\n');print(json.dumps({'status':'PASS','checks':len(rows),'mode':sys.flags.optimize}))
