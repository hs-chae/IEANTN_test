"""Replay new analytic cells and rays; also check finite receipt comparisons.
Generate the finite receipts afresh with their corresponding scripts first if desired.
"""
from d02_cert import *
from pathlib import Path
s=D(".75"); k=D(".275")
elementary()
mverify_common()
lt(I("2.45")/(2*pi*E(1)),1)
lt(2*pi*E(1),51)
lt(I(2).log(),1)
lt(3*E(-188)+(I("1.2")*c+351*E(-100))/200**2,"4e-17")
lt(I("1.415")+I("1.000000147"),"2.415001")
lt(1+I(1)/100+2/I(100)**2+remainder(2,I(100)),1.02)
lt(2*(1+I(1)/100+2/I(100)**2+remainder(2,I(100)))+local(I(100),CAP0,s,k)+Wpi(100,CAP0)+Vpi(100),2.05)
lt(I("1.01")*E(R2)+I("2.05"),"3.24")
for a,b,q,pv,n in [
  ("36.528","36.531",".001",True,0),("36.531","36.737",".002",True,0),
  ("36.737","36.890",".1",True,0),("36.890","39.326",".168",True,0),
  ("36.98","37.5",".207",True,0),("39.326","39.912",".168",False,0),
  ("39.912","42.471",".4",False,0),("40","42.471",".431",False,0),
  ("42.471","60","1",False,0),("45","76","1.212",False,0),
  ("46","68","1.241",False,0),("47","63","1.264",False,0),("48","55","1.308",False,0),
  ("49","52","1.321",False,0),("59","73","1.220",False,0),("75","100","1.152",False,0),
  ("47.02","58","0",False,5),("58","100","0",False,5),("100","190","0",False,5),
  ("52.1","125","0",False,6),("57.5","91","0",False,7),("64","66","0",False,8),
  ("100","175","1.0820",False,0),("100","172.1","1.0837",False,0)]:
    cells(a,b,q,CAP0,pv,n)
for a,b,q in [("100","175","1.0838"),("100","175.3","1.0837"),("175","190","1.0777")]:
    cells(a,b,q,CAP2)
for l in Path("optimized.log").read_text().splitlines():
    if l.startswith("factorial "):
        _,b,n,a,m,sv,kv,eta,*_=l.split()
        compare(int(n),a,int(m),D(b),D(sv),D(kv),eta)
for n,a in [(12,420),(17,561),(32,982),(64,1874),(100,2875)]:
    compare(n,a,n+8,CAP2,None,k)
for n,a in [(6,253),(12,421),(17,562),(32,983),(64,1875),(100,2876)]:
    compare(n,a,n+8,CAP2,"raw",k)
# Constants for symmetric exact-Li gaps at the same onset, 201.
for b,z,Q in [(CAP0,R0,".060"),(CAP2,R0,".00161"),(CAP2,R2,".831")]:
    mdecreasing(200,b,s,k,z)
    lt(I("3.24")*E(I(z)*200)*(local(I(200),b,s,k)+Wpi(200,b)+Vpi(200)),Q)

power(14,"188.5",CAP0,".125",".01908")
whole=[("14",".125",".01111"),("14",".13",".01191"),("14",".135",".01278"),
       ("14",".14",".01920"),("14",".145",".04461"),("14",".15",".10363"),
       ("14",".15625",".2973"),("13",".125",".01677"),("13.5",".125",".01363"),
       ("15",".125",".00741"),("16",".125",".00498"),("17",".125",".003358"),
       ("18",".125",".002275"),("19.03",".125",".001537")]
for a,z,K in whole:power(a,"168.6",CAP2,z,K)
tailrows=[(170,".275",None,".29473",".001453"),
          (180,".275",None,".27903",".001007"),
          (200,".275",".018221",".25594",".000495"),
          (250,".275",".015899",".22294",".00009021"),
          (300,".275",".014652",".20535",".00001742"),
          (500,".25",".012654",".17733","2.904e-8"),
          (1000,".225",".011454",".16057","4.305e-15"),
          (3000,".20",".010761",".15079","2.906e-42"),
          (30000,".20",".010476",".146743",None),
          (1000000,".20",".010446",".146320",None)]
for a,k0,h0,h2,j2 in tailrows:
    for b,z,Q in [(CAP0,R0,h0),(CAP2,R2,h2),(CAP2,R0,j2)]:
        if Q:
            mdecreasing(a,b,s,D(k0),z)
            v=mcoef(a,b,s,D(k0),z)
            lt(v,Q)
            print("uniform power tail",a,b,z,Q,v.b)
for b,lo,hi in [(CAP0,".01044",".01045"),(CAP2,".14630",".14631")]:
    lt(lo,2*knot(b)+I("4e-12"));lt(2*knot(b)+I("4e-12"),hi)
# Comparison with any old power row in the portfolio and the CH2 floor.
lt(I(".29473")*E(-I(170)/32),".01044")
lt(I(".29473")*E(-I(R2)*170),c)
lt(I(".29473")*170**2*E(-I(R2)*170),".043")
lt(87,32*(I(".2973")/I(".01908")).log());lt(32*(I(".2973")/I(".01908")).log(),88)
lt("168.47",32*(I(".2973")/I(".001537")).log());lt(32*(I(".2973")/I(".001537")).log(),"168.48")
for Q,r in [(".01908",R0),(".2973",R2)]:
    for onset,C,lo,hi in [(2278382,".2",40,41),(2278383,".2",40,41),(912560,".3",34,35)] if r==R0 else [
                         (2278382,".2",53,54),(2278383,".2",53,54),(912560,".3",50,51)]:
        a=I(onset).log(); h=lambda x:I(Q)*I(x)**2*E(-I(r)*x)
        if r==R0: lt(a,16)
        else: lt(2/I(r),a)
        lt(C,h(a));lt(C,h(lo));lt(h(hi),C)
# Density-free local exponent still beats the old pure rate, though with log cost.
L=I(200)
h=mW(L,CAP2,None,D(".25"),R2)
lt(h*E(h*E(-I(R2)*L)/L)/L**2,".01421")
for a,z,Q in [(600,".125",".000037"),(1000,".14",".00125")]:
    # Use the already verified ratio .01421 only beyond the indicated extremum.
    lt(2/(I(R2)-I(z)),a)
    lt(I(".01421")*a*a*E((I(z)-R2)*a),Q)
r=I(R2)
w=(L*L+(L*L+2*L/r+2/r**2)/r)/64+V(L)*E(r*L)
p=(L+(L+1)/r+1/r**2)/64+V(L)*E(r*L)/L
lt(w/L**2,".123");lt(p*E(p*E(-r*L))/L,".120")
# Direct local input is larger than the old density bound at 200; at 500
# even the direct absolute-transform branch beats old pure power constants.
lt(dense(L,True),L**2*E(-L/32)/64)
lt(I(".123")*500**2*E(-I(500)/32),".01044")
# Finite log comparisons; the generator scripts prove every cell of these receipts.
def rows(file,kind):
    lines=Path(file).read_text().splitlines()
    a=[l.split() for l in lines if l.startswith(kind+" ")]
    off=len(kind.split())
    return {D(row[off]):list(map(D,row[off+1:])) for row in a}
pr=rows("finite_d02.log","prod"); we=rows("finite_d02.log","weighted")
pr2=rows("finite_extended.log","prod"); we2=rows("finite_extended.log","weighted")
pw=rows("power_new.log","finite power scaled upper")
for a,pq,e in [("2278381.72",".2",None),("2278381.75",".199997",None),
    ("2278382",".199973",None),("2278382.12",".2",".2"),
    ("2278383",".199879",".199917")]:
    x=pr[D(a)];lt(max(x[:2]),pq)
    if e:lt(x[2],e)
for a,Q in [("912559.9975",".3"),("912560",".29999946")]:lt(we[D(a)][0],Q)
closepoly=[(15000000,".09574",".10246"),(18000000,".09394",".10059"),(20000000,".08875",".09479"),
           (25000000,".08810",".09334")]
for a,Q,Vv in closepoly:lt(max(pr[a]),Q);lt(we[a][0],Vv)
extrapoly=[(40000000,".07019",".07483"),(50000000,".05620",".06036"),
          (60000000,".05609",".05910"),(150000000,".04467",".04709"),(200000000,".043",".043")]
for a,Q,Vv in extrapoly:lt(max(pr2[a]),Q);lt(we2[a][0],Vv)
for a,Pv,Wv in [(70000,".01946",".02138"),(100000,".01908",".02080"),(104000,".01908",".01908")]:
    lt(max(pw[a][:2]),Pv);lt(pw[a][2],Wv)
bridges=[(100000,".01895",".02080"),(104000,".01724",".01876"),(180000,".01469",".01598"),
 (250000,".01363",".01469"),(400000,".01104",".012001"),(500000,".01020",".01103"),
 (700000,".00849",".00919"),(1000000,".00807",".00870"),(1200000,".00753",".00816"),
 (1500000,".00737",".00793"),(2000000,".00608",".00654"),(2500000,".005752",".006141"),
 (4000000,".004622",".004957"),(5000000,".004340",".004675"),(6000000,".004047",".004335"),
 (8000000,".003549",".003809"),(10000000,".003456",".003676"),(15000000,".003358",".003358")]
for a,Pv,Wv in bridges:
    lt(max(pw[a][:2]),Pv);lt(pw[a][2],Wv)
    lt(".0033571",min(D(Pv),D(Wv)))
lt(power(17,"168.6",CAP2,".125"),".0033571")
lt(16,I(40000000).log())
lt(max(max(pr[40000000]),we[40000000][0])*E(I(18)/8)/18**2,".002275")
lt(max(max(pr2[150000000]),we2[150000000][0])*E(I("19.03")/8)/I("19.03")**2,".001537")
lt(16,I(150000000).log())
lt(E("19.03"),300000000)
print("all signed envelopes, finite joins, and crossover tests passed")
