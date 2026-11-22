#!/usr/bin/env python3
"""Directed Arb comparison of full published functions. No actual M evaluation,
no proof of the pending analytic candidate, and no source-first PV claim."""
import argparse,json,hashlib,time,sys
from pathlib import Path
from flint import arb,ctx
ctx.prec=256
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
if a.out.exists():raise ValueError('fresh output required')
started=time.monotonic();q=lambda x:arb(str(x));pi=arb.pi();e=q(1).exp();H=q(3000175332800);logH=H.log();llH=logH.log()
s21=[('.999','4.487','.517'),('.99','4.543','.505'),('.9','5.255','.408'),('.85','5.837','.362'),('.8','6.654','.322'),('.75','7.865','.286'),('.7','9.798','.254'),('.65','13.003','.227'),('.6','19.53','.202'),('.55','39.121','.179')]
jlt=[('4/5','.00780973',43),('27/20','.0609073',93),('2/3','.00255758',161),('10/9','.0130895',192),('19/12','.0912303',233),('31/16','.430429',288),('47/20','4.88346',385)]
# Read the OUTPUT k/cM/logxM columns, not A/alpha/B/beta inputs.
frac=lambda s:q(s.split('/')[0])/q(s.split('/')[1])if'/'in s else q(s)
ll1=[('5.56','1237','4589.20'),('6','793','4952.38'),('7','701','5777.77'),('8','686','6603.17'),('10','678','8253.96')]
ll2=[('21.24','1980','10352.03'),('21.5','942','10490.06'),('22','790','10755.87'),('25','731','12360.29'),('30','721','15066.77')]
ll3=[('53.99','6368','10.01'),('54','5223','10.01'),('55','488','10.03'),('60','473','10.11'),('70','467','10.27')]
def old21(L):return q('.6').log()+L.log()-L/2+q('5.2251')*L/(L/2+(3*e/2).log()).log()
def new(L):return q(1100000).log()-q(25)/132*L
def profiles(L):
 out=[]
 def add(name,v,source,domain):out.append({'id':name,'log_of_normalized_upper':str(v),'source':source,'domain':domain,'new_strictly_smaller':bool(new(L)<v)})
 add('trivial',q(0),'|M|<=x','x>=1')
 add('Simonic2023_Thm2',(q('555.71')*(-L/100).exp()+q('1.94e14')*(-L/50).exp()).log(),'published Thm2(7), PDFp4','x>=1, RH')
 add('JLT_ThmA1_headline',q('2.91890').log()-2*L.log(),'2408.04143v3 ThmA1(A.5), PDFp27','x>1')
 if L>=q(2160535).log():add('CohenDressMarraki',-(q(4345).log()),'JLT PropositionA3(A.11), PDFp28','x>=2160535')
 if L>=q(1798118).log():add('RZA_full',(q('.006688')*L-q('.039')).log()-2*L.log(),'2408.05969v2 Thm1.1','x>=1798118')
 for k,c,on in jlt:
  if L>=on:add('JLT_output_k_'+k,q(c).log()-frac(k)*L.log(),'2408.04143v3 Table1, PDFp32','logx>='+str(on))
 if L>=q(10).log()*q(10)**q('4.487'):add('Simonic2021_full',old21(L),'2109.11744v2 Thm2(9)','x>=10^(10^4.487), RH')
 for alpha,X,A in s21:
  if L>=q(10).log()*q(10)**q(X):add('Simonic2021_alpha_'+alpha,q(A).log()+L.log()-(1-q(alpha))*L,'2109.11744v2 Thm2(11),Table1','logx>=log10*10^'+X+', RH')
 for W,R,on in ll1:
  if L>=q(on):
   W,R=q(W),q(R);c=2*e+12*R/(23*pi*W)*(L/W)**(-q(1)/24)+4*(2+1/L).exp()/(W*L).sqrt()
   add('LeeLeong_full_classical_W_'+str(W),c.log()+L.log()-(L/W).sqrt(),'2208.06141v5 PDFp5 Thm2.2(17), unnumbered c1 above; Table1 PDFp4','logx>='+on)
 for W,R,on in ll2:
  if L>=q(on):
   W,R=q(W),q(R);c=2*e+(1+3/(4*llH))*12*R*llH**q('.25')/(23*pi*W*logH**(q(1)/12))+4*(2+1/L).exp()*(L.log()/(W*L)).sqrt()
   add('LeeLeong_full_Littlewood_W_'+str(W),c.log()+L.log()-((1-W.log()/L.log())*L*L.log()/(2*W)).sqrt(),'2208.06141v5 PDFp5 Thm2.2(18), unnumbered c2 above; Table1 PDFp4','logx>='+on)
 for W,R,on in ll3:
  if L>=q(on).exp():
   W,R=q(W),q(R);c=2*e+3*R/(5*pi*W*llH**(q(1)/12))+4*(2+1/L).exp()/(W**q('.6')*L**q('.4'))
   v=c.log()+L.log()-(5/(3*W**3)/(1-W.log()/L.log()))**q('.2')*L**q('.6')/L.log()**q('.2')
   add('LeeLeong_full_KV_W_'+str(W),v,'2208.06141v5 PDFp5 Thm2.2(19), unnumbered c3 above; Table1 PDFp4','loglogx>='+on)
 return out
rows=[]
for Lint in [100,132,200,300,1000,10000,100000,1000000,10000000,100000000]:
 L=q(Lint);pr=profiles(L);rows.append({'logx':Lint,'new_log_normalized_upper':str(new(L)),'new_M_over_x':str(new(L).exp()),'new_weighted_m_upper':str((q(6908000).log()-q(25)/132*L).exp()),'new_strictly_below_every_profile_in_this_explicit_catalog':all(z['new_strictly_smaller']for z in pr),'profiles':pr})
lo,hi=10000000,100000000
if not new(q(lo))<old21(q(lo)) or not new(q(hi))>old21(q(hi)):raise ValueError('crossing bracket signs differ')
while hi-lo>1:
 mid=(lo+hi)//2;d=new(q(mid))-old21(q(mid))
 if d<0:lo=mid
 elif d>0:hi=mid
 else:raise ValueError('undecided directed comparison')
result={'status':'DIRECTED_FULL_FUNCTION_COMPARISONS_ONLY_NOT_RH_TO_M_PROOF','source_first_PV':False,'precision_bits':ctx.prec,'python':sys.version,'python_flint':'0.9.0','source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'parameter_seeds':None,'rows':rows,'Simonic_full_crossing_sign_bracket_logx':[lo,hi],'crossing_uniqueness_proved':False,'elapsed_seconds':time.monotonic()-started}
a.out.parent.mkdir(parents=True,exist_ok=True);tmp=a.out.with_suffix('.tmp');tmp.write_text(json.dumps(result,indent=2)+'\n');tmp.replace(a.out)
print('completed',len(rows),'points; crossing sign bracket',lo,hi)
