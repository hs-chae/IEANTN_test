"""Exact rational endpoint checks for the paper inequalities (NOT source PV)."""
from ram_cert import Q, expi, logi, p, req

def hi(x): return expi(Q(x))[1]
def lo(x): return expi(Q(x))[0]
A=Q(1)/(8*Q("3.141592"))
PI_HI=Q(22,7)
PI_LO=Q("3.141592")
l=Q(34)
c=Q(".0462"); b=Q("1.838")
req(20*lo(17)/l>10**7)
req((PI_HI*(1+Q(1,10**7-1))+PI_HI**2/10**7)/20 < Q(".158"))
req(Q("1.15")<logi(10/PI_HI)[0] and logi(10/PI_LO)[1]<Q("1.16"))
req(Q("3.52")<logi(l)[0] and logi(l)[1]<Q("3.53"))
req((4*Q("2.38")**2+Q(4,3)*Q("2.38"))/l<Q(".77"))
req(3*Q("3.52")-4*Q("1.16")+Q(2,3)-8*PI_HI*Q(".158")>Q("2.61"))
req(-A*hi(4)*Q(".48")+Q("1.465")*Q("3.52")+Q("1.2325")>0)
req(A*17**2*hi(Q(-17,2))<Q(".003"))
req(Q("1.03883")*(hi(-l/6)+hi(-3*l/10))<Q(".004"))
req(Q("1.94")*hi(4)/8+c*hi(4)/64+2*b/64+5*b/32<14)
req(p(3,Q(17))+Q(72,17**4)+A*17**2*hi(Q(-17,2))<Q("1.071"))
req(2*(hi(-l/6)+l/logi(Q(2))[0]*hi(-l/4))<Q(".028"))
req(Q(".821")+Q("1.10")+Q(".278")/l+14*l*hi(-l/2)<Q("2.4"))
req(Q("1.8")*l/(8*PI_HI)>Q("2.4"))
print("PNT scalar guards checked, including reduced-sum loss 0.821.")

req(5*c+3*b*hi(-l/2)<Q(".232"))
req(c*(5+7/l+4/l**2)+b*hi(-l/2)*(3+4/l+2/l**2)<Q(".241"))
S=A/2*l*((Q(7,6)*l+Q(8,9))*hi(-l/4)+l*hi(-l))
req(S<Q(".006"))
req(1-2/l-hi(-l/2)/2-Q(".006")>Q(".935"))
req(l*hi(-l/6)<Q(".118"))
req(A*hi(-l/4)*(Q(7,3)*(l/2)**2+Q(16,9)*(l/2)+Q(32,27))<Q(".01"))
req(10*hi(-l/6)<Q(".035"))
req(l*hi(-l/2)/(2*(1-hi(-l)))<Q(".001"))
req(Q("1.04")*A*l*hi(-l/2)<Q(".000002"))
req(logi(4*PI_LO)[0]>Q("2.531"))
req(Q(".047")*(1+1/l)+2*hi(-l/2)<Q(".049"))
req(Q(".047")+2*hi(-l/2)<Q(".048"))
print("Weighted scalar guards checked for both signed-tail routes.")

l=Q(40)
req(lo(l/2)/(Q(5,2)*PI_HI)>Q("14.14"))
req(4-logi(3*PI_LO**2)[0]<Q(".62"))
req((4+2*PI_HI)/l<Q(".258"))
req(3*hi(-l/6)<Q(".004"))
req((l*l+8)*3*l*hi(-l/2)<Q(".001"))
req(2*3*l*hi(-l/2)<Q(".00001"))
req(Q(".62")+Q(".258")+Q(".004")+Q(".001")+Q(".00002")<Q(".9"))
print("Direct interval scalar guards checked at L=40.")

# Fourier route scalar guards at x=4e18 (on the upper cap c=4.4
# except for the logarithmic lower bound, c >= 2.63).
x=Q(4*10**18); rt=Q(2*10**9)
ln2=logi(Q(2))[0]
req(42<logi(x)[0]<logi(x)[1]<43)
req(Q("4.4")*43/(4*PI_LO*rt)<Q("1e-8"))
req(Q("4.4")**2*43**2/(2*rt)<Q("1e-5"))
req(68*43**2/rt<Q(".001"))
req(12*PI_HI**2/(Q("2.63")*ln2*42)*rt*(2/x)**2<Q(".001"))
req(43/rt<Q(".001"))
req(Q(".959")/Q(".83")<Q("1.16"))
req(logi(Q("2.63")*ln2*42/2)[0]>3)
req(Q("4.4")**2*43**2/(4*rt)<Q(".001"))
print("Fourier direct count scalar guards checked on the explicit ray.")

# Two-range zero-count scalar; the partial summation is a written proof.
a=2*PI_LO
req(logi(Q(280))[1]<6)
req(Q("8.066")**2/a+Q(7,4)/a+2*(Q(6,5)+Q(6,5))/280<Q("10.651"))
req(Q("10.651")-Q("10.3194")<Q(".332"))
print("Two-range inverse-ordinate guard: cap 10.651 and additive loss .332.")
