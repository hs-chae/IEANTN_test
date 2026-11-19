"""Sharpened spectral radius and logarithmic/four-error certificates."""
from mertens import *
SP=[spectral(b,step=Q('.000125'),tighter=True) for b in (B0,B1)]
D=coefficient(Q('.77'),True)
assert (116-D).yes()
# Both constants checked independently in verify.basic and the anchor script.
pi_hi=Q('3.141594')
assert ((ln(H)-ln(2*pi_hi))**2/(4*pi_hi)-Q('.9321')-55).yes()
def spec(L,mode,scaled=False):
 a= [Q(1,8),Q(5,32)][mode] if scaled else Q(0)
 g=shifted(L,SP[mode],a)
 # Remove the finite-RH mass and the lower end of the discrete layer.
 if L>=100:
  g-=(55+D)*ex(-L*(Q('.23')-a))
 return g

def jnew(L,b,k):
 if k==0:return J(L,b,0)
 return (1/L+1/L**2)*J(L,b,0)

def tailbetter(L):
 # A symmetric monotone theta error cap for EVERY v >= t.
 def eps(t):
  p=mix(t,CH+POWER)
  d=Q('20.83')/t**3
  if t>=ln(10).b*4/S and t<=Q('29.933'):
   f=mix(t,[(I('1.751000147'),0,Q(1,2)),POWER[1]])
   # the finite lemma expires at 29.933; use the CH floor branch thereafter
   p=mn(p,mx(f,mix(Q('29.933'),CH+POWER)))
  if t<=58 and t>=7:
   p=mn(p,mx(weight(t,2,Q(1,2))/PI8,mix(Q(58),CH+POWER)))
  return mn(p,d)
 e2,e3=eps(L/2),eps(L/3)
 return (1+3*e2)*ex(-L/2)+(2*(1+e3)+(1+5*e3)/2/(1-ex(-L/3)))*ex(-2*L/3)

def rad(L,b,g=None):
 # Branches deliberately cut at rational safe log thresholds.
 p=mix(L,CH)
 if L<=58:p=mn(p,weight(L,2,Q(1,2))/25)
 if L<=Q('29.933'):p=mn(p,Q('.791')*ex(-L/2))
 if L>=24:
  for m,bias in CG:p=mn(p,mix(L,m)+bias)
 if L>=40:p=mn(p,spec(L,b) if g is None else g)
 return p

def pc(L,b):
 assert L>=120
 a=[Q(1,8),Q(5,32)][b]
 assert Q(2)*L/(L*L-48*170)<Q('.23')-a
 assert all(d<=(r-a)*L for c,d,r in SP[b])
 g=spec(L,b,True)
 # For monotone tail use the original logarithmic theta tail majorant.
 j=Q('.1')*ex(-(Q(1,2)-a)*L)+Q('1e-11')+Q('2.1')*ex(-(1-a)*L)
 e2=Q('20.83')/(L/2)**3;e3=Q('20.83')/(L/3)**3
 tail=(1+3*e2)*ex(-(Q(1,2)-a)*L)+(2*(1+e3)+(1+5*e3)/2/(1-ex(-L/3)))*ex(-(Q(2,3)-a)*L)
 w=g+j+tail
 p=g+(1+1/L)*j+tail
 assert p.yes() and (1-p).yes()
 return w,p*(1+2*p*ex(-a*L)/L),p

def earlypc(L,V,b):
 a=[Q(1,8),Q(5,32)][b]
 cap=CH[0][0]*ex(a*V)+CH[1][0]*ex(-(Q(1,2)-a)*L)
 # All corrections decrease after scaling from L >= 40; retain old tail for this proof.
 h=cap+ex(a*L)*(jnew(L,b,0)+tail1(L))
 p=cap+ex(a*L)*(L*jnew(L,b,1)+tail1(L))
 assert (1-p).yes()
 return max(q.b for q in [h,p*(1+2*p*ex(-a*L)/L)]+list(pc(V,b)))

def finitepower(b):
 # Every cell up to 40, with the only upward cutoff explicitly split.
 a=[Q(1,8),Q(5,32)][b]
 ends=sorted({Q(j,20) for j in range(200,801)}|{Q('29.933')})
 result={}; best=I(0)
 for l,r in reversed(list(zip(ends,ends[1:]))):
  d=rad(l,b)
  if l==Q('29.933'):
   right=weight(l,2,Q(1,2))/25
   for m,bias in CG:right=mn(right,mix(l,m)+bias)
   d=mx(d,right)
  tail=tailbetter(l)
  h=d+jnew(l,b,0)+tail
  p=d/l+jnew(l,b,1)+tail/l
  assert (Q(1,2)-p).yes()
  v=ex(a*r)*mx(h,r*p*(1+2*p))
  best=mx(best,v)
  if l.denominator==1:result[int(l)]=best
 return result

def specgrid(b):
 # Evaluate the same expression at exact gridpoints by an outward recurrence.
 L=Q(40); step=Q(1,10); terms=SP[b]
 factors=[ex(-step*a) for c,d,a in terms]
 parts=[c*ex(-L*a) for c,d,a in terms]
 a0=Q('.23'); bot=(55+D)*ex(-L*a0); br=ex(-step*a0)
 out={}
 for j in range(400,3201):
  L=Q(j,10)
  out[L]=sum(part*L**d for part,(_,d,_) in zip(parts,terms))-(bot if L>=100 else 0)
  parts=[v*w for v,w in zip(parts,factors)]
  bot*=br
 return out

def logs(b):
 # Exact outward intervals over closed log cells, plus a monotone infinite tail.
 # Right limits at the old cutoffs bounded using CH and the *other* active branches.
 from verify import basic
 ends=sorted({Q(j,10) for j in range(160,3201)}|{Q('29.933')})
 acc={k:I(0) for k in (2,3,4,5,6,7,8,9)}
 w,p,_=pc(Q(320),b)
 a=[Q(1,8),Q(5,32)][b]
 for k in acc:acc[k]=(p if k%2 else w)*ex(-a*320)*320**(k-1 if k%2 else k)
 out={}; grid=specgrid(b)
 for l,r in reversed(list(zip(ends,ends[1:]))):
  d=rad(l,b,grid.get(l))
  if l in [Q('29.933'),Q(58)]:
   vals=[mix(l,m)+bias for m,bias in CG]
   if l==Q('29.933'):vals.append(weight(l,2,Q(1,2))/25)
   if l==Q(58):vals.append(spec(l,b))
   right=vals[0]
   for v in vals[1:]:right=mn(right,v)
   d=mx(d,right)
  # eps(t) is itself monotone for all t >= 16/3; see enhanced.md.
  tail=tailbetter(l)
  w=d+jnew(l,b,0)+tail
  p=d/l+jnew(l,b,1)+tail/l
  assert (Q(1,2)-p).yes()
  p=p*(1+2*p)
  for k in acc:acc[k]=mx(acc[k],(p if k%2 else w)*r**k)
  if l.denominator==1:out[int(l)]=acc.copy()
 return out


POWERS=[
 (0,190,'.01291'),(0,219,'.0115'),(0,225,'.01128'),(0,310,'.0095'),
 (0,320,'.009374'),(0,450,'.008406'),(0,800,'.007565'),
 (0,1000,'.007375'),(0,2000,'.007024'),(0,5000,'.006831'),
 (1,140,'.34621'),(1,160,'.27855'),(1,172,'.254'),(1,175,'.24845'),
 (1,196,'.222'),(1,200,'.21726'),(1,250,'.18519'),(1,288,'.172'),
 (1,300,'.16872'),(1,500,'.14330'),(1,860,'.131'),
 (1,1000,'.12878'),(1,2000,'.12259'),(1,5000,'.11918')]
NEWLOG=[
 (0,16,2,'.194','.1958'),(0,17,2,'.1292','.1303'),
 (0,18,2,'.08584','.08655'),(0,20,2,'.03731','.03759'),
 (0,22,2,'.01621','.01632'),(0,24,2,'.009626','.009649'),
 (0,32,2,'.004129','.004142'),(0,40,2,'.0001825','.0001830'),
 (0,40,4,'.2934','.2942'),(0,55,2,'4.005e-7','4.012e-7'),
 (0,65,2,'3.627e-8','3.629e-8'),(0,55,4,'.001257','.001257'),
 (0,55,6,'43.502','43.526'),(0,200,6,'10.997','11.003'),
 (0,40,8,'1506607','1507417'),
 (1,65,2,'2.956e-8','2.958e-8'),(1,55,4,'.001216','.001218'),
 (1,65,4,'.0008342','.0008347'),(1,55,6,'23.545','23.559'),
 (1,175,6,'9.544','9.550'),(1,200,6,'.37390','.37409'),
 (1,40,8,'758563','760494'),(1,55,8,'664513','664909'),
 (1,175,8,'292609','292776'),(1,200,8,'14971','14979')]

def late():
 # Analytic bound on the logarithmic derivative of D4, independent of mesh.
 a_min=1-8*(1-Q('.77'))/3
 lh=ln(Q(h.b,S))
 assert (150-((8* (h+ln(3)))/3+2*lh+Q(40,3)/a_min+
              sum(2/(Q(13,4)-i) for i in range(4)))).yes()
 t=Q(1000)
 for b,c in [(0,Q('.006750')),(1,Q('.11826'))]:
  aa=[Q(1,8),Q(5,32)][b]
  v=shifted(t,SP[b][:5],aa)
  # No rescaling error loss: cap decaying terms on the whole L >= 1000.
  et=Q('20.83')/(t/3)**3
  tail=(1+3*et)*ex(-(Q(1,2)-aa)*t)+(2*(1+et)+(1+5*et)/2/(1-ex(-t/3)))*ex(-(Q(2,3)-aa)*t)
  js=(1+1/t)*(Q('.1')*ex(-(Q(1,2)-aa)*t)+Q('1e-11')+Q('2.1')*ex(-(1-aa)*t))
  assert (Q('1.01e-11')-(v+tail+js)).yes()
  L=Q(100000)
  r=coefficient((B0,B1)[b],True)*L/(L-150)+Q('1.01e-11')
  # e^{-aa L} <= e^{-aa * 1000}; no underflow multiplication.
  assert (c-r*(1+2*r*ex(-aa*t)/L)).yes()
  print('continuous far power',b,L,c,flush=True)

def run():
 from verify import basic
 assert (I(10)-4*ln(10)).yes() and (ex(7)-599).yes()
 assert Q(200)/(100**2-48*170)<Q('.23')
 for b,u,c in POWERS:
  assert all((Q(c)-z).yes() for z in pc(Q(u),b)),(b,u,c)
  print('sharper power',b,u,c,flush=True)
 for b,u,V,c in [(0,14,Q('185.97'),Q('.01318')),(1,10,Q('167.94'),Q('.2612'))]:
  assert earlypc(Q(40),V,b)<I(c).a
  q=finitepower(b)[u]; assert (c-q).yes()
  print('early continuous power',b,u,V,c,flush=True)
 l=ln(368359)
 assert (I(14)-l).yes() and (Q('.01318')-Q('.4')*exp(l/8)/(l*l)).yes()
 print('early B0 power from finite join',368359,flush=True)
 assert (ex(Q(140,32))-Q('.34621')/Q('.006750')).yes()
 late()
 for b in (0,1):
  out=logs(b)
  for mode,u,k,cw,cp in NEWLOG:
   if mode==b:
    assert (Q(cw)-out[u][k]).yes() and (Q(cp)-out[u][k+1]).yes(),(b,u,k,cw,cp)
    print('sharper log',b,u,k,cw,cp,flush=True)
if __name__=='__main__':run()
