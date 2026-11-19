"""Integer fixed-point weighted prime-sum join, not a floating sample."""
from verify import I
from early import primes,N
from decimal import Decimal as D,ROUND_FLOOR,ROUND_CEILING
S=10**20
N1=66000000
def ceildiv(a,b):return (a+b-1)//b
def scale(a):
    w=I(a)*S
    return (int(w.a.to_integral_value(rounding=ROUND_FLOOR)),
            int(w.b.to_integral_value(rounding=ROUND_CEILING)))
def logs(args):
    n=stop=0
    for p in args:
        if p>=stop:
            n=p;stop=n+max(1,n//2048)
            a,b=scale(I(n).log())
            n2=n*n;n3=n2*n
        h=p-n;h2=h*h
        yield (p,a+S*(2*n*h-h2)//(2*n2),
               b+ceildiv(S*(6*n2*h-3*n*h2+2*h*h2),6*n3))
def main():
    n=100000
    g=sum(I(1)/i for i in range(1,n+1))-I(n).log()-I(1)/(2*n)
    b,c=scale(g+I(0,(I(1)/n**2).b))
    N=25000000
    for p,l,u in logs(primes(N)):
        d=p*(p-1)
        b+=l//d
        c+=ceildiv(u,d)
    main=-(1-I(1)/N).log()
    err=I('.2')/I(N).log()**2*(I(2)/(N-1)+main)
    v,w=scale(main)
    e=scale(err)[1]
    b+=v-e
    c+=w+e
    lo,hi=0,0
    last_l=last_u=0
    targets={912000:0,912500:0,912550:0,912558:0,912559:0,D('912559.995'):0,D('912559.998'):0,D('912559.999'):0,D('912559.9995'):0,912560:0,1000000:0,2000000:0,3000000:0,5000000:0,10000000:0}
    clips={x:scale(I(x).log()) for x in targets}
    def check(p,l,u):
        # prefix after the preceding prime, over the entire cell up through p^-
        nonlocal lo,hi,last_l
        # First-cell clipping uses L>=log x. Skip the pre-jump cell if p==x
        # unless p is the nonprime final artificial endpoint.
        for x,m in targets.items():
            if p>x:
                a,d=clips[x]
                pos=max(0,hi+c-max(last_l,a))
                assert pos<S
                z=max(max(0,u-b-lo)*u*u,pos*max(last_u,d)**2)
                targets[x]=max(m,z)
    for p,l,u in logs(primes(N1)):
        check(p,l,u)
        lo+=l//p
        hi+=ceildiv(u,p)
        last_l=l;last_u=u
    l,u=scale(I(N1).log())
    check(N1,l,u)
    assert (I(18).exp()).b<N1
    for x,m in targets.items():
        print('weighted scaled upper',x,(I(m)/S**3).b)
if __name__=='__main__':main()
