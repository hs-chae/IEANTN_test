import d02_ram_new as R
from d02_density_new import Q,D,D0,mass,el
from math import factorial
import sys
onsets = {
20: [172,187,212,237,263,289,316,343,369,396,423,451,478,505,535],
40: [559,587,614,641,669,696,724,751,778,806,833,861,888,916,943,971,998,1026,1053,1084],
80: [1108,1136,1163,1191,1218,1246,1273,1301,1328,1356,1383,1411,1439,1466,1494,1521,1549,1576,1604,1631,1659,1687,1714,1742,1769,1797,1824,1852,1879,1907,1935,1962,1990,2017,2045,2073,2100,2128,2155,2186],
}
finite = [
 ('47.647', 172, 6, '8.39'),
 ('47.677', 172, 6, 10),
 ('47.955', 172, 6, 25),
 ('48',     172, 6, 27),
 ('48.27',  172, 6, 40),
 ('48.49',  172, 6, 50),
 ('49.30',  172, 6, 80),
 ('49',     172, 6, 70),
 ('172',    176, 6, 95),
 ('176',    187, 6, 120),
 ('180',    187, 6, 133),
]
tails = [(172,6,93), (176,6,119), (180,6,133)]
def statement(a,b,j,z,d=D):
    y,n,h,u,v=R.adapt(a,b,j,z,d)
    print('join',d,a,b,j,z,'PASS' if y else 'FAIL',n,float(h),float(u),float(v),flush=True)
    return y
def ray(a,j,z,n,d=D,passes=True):
    t=R.end(a,j,z,n,d)
    print('tail',d,a,j,n,str(z),'slack/C_j',float(t/R.polys(n)[0][j]),flush=True)
    if passes:assert t>0
    return t
if __name__=='__main__':
    mode=sys.argv[1:]
    if mode==['finite']:
        success=[]
        for row in finite:success.append(statement(*row))
        for r in [('49.31',172,6,'80.6'),('52.99',122,7,0),('53',123,7,0),
                  ('56',106,7,1050),('56',105,7,1060)]:
            y,n,w,a,b=R.adapt(*r,panels=128,depth=19)
            print('fine cells',r,y,n,float(w),float(a),float(b),flush=True)
            success.append(y)
        assert all(success)
    elif mode==['scout_failure']:
        for row in [('49.30',172,6,81),('47.64',172,6,10),('49.27',172,6,80)]:
            statement(*row)
        ray(559,21,0,40,D0,passes=False)
    else:
        a=Q(559); j=21
        P=mass(D0,1)[-2][1]
        c=R.polys(40)[0]
        shifted_debit=a**j*a/(a-1)*P*el(-D0*(a-1))
        allowance=sum(Q(c[k])*a**(j-k) for k in range(j,41))
        assert shifted_debit>allowance
        print('matched B0: lower bound on shifted sufficient debit / available polynomial',
              float(shifted_debit/allowance),flush=True)
        for n in R.ANC:R.anchor(n)
        for n,lst in onsets.items():
            j=6 if n==20 else n//2+1
            for k,a in enumerate(lst,j):
                ray(a,k,100 if k==6 else 0,n)
        for n,a in [(20,546),(40,1096),(80,2197)]:
            ray(a,n,Q(R.polys(n)[0][n],2),n)
        for a,j,z in tails:ray(a,j,z,20)
        for a,j,z,n in [('171.85',6,100,20),('211.5',8,0,20),('1083.9',40,0,40),('2185.9',80,0,80)]:
            ray(a,j,z,n)
        ray(2889,80,0,80,D0)
        ray(2899,80,Q(R.polys(80)[0][80],2),80,D0)
