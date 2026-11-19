from cert import exp_bounds, ln_bounds, F
import sys
D={int(n):(int(p),int(q)) for n,p,q in map(str.split,open(sys.argv[1]))}
N=38358837682; K=14111427770; A=1644673232; B=632207037
assert D[N-1][0]==D[N+1][0]==A and D[N+1][1]==0 and D[K-1][0]==B
e0,e1=exp_bounds(1)
assert K*e1<N and N+1<(K+1)*e0
for q,s in [('.2179263651446',-1),('.2179263651448',1),('.2',-1)]:
    x=N+F(q);l,h=ln_bounds(x)
    a,b=e0*B*x/h-A*A,e1*B*x/l-A*A
    assert b<0 if s<0 else a>0
l,h=ln_bounds(N)[0],ln_bounds(N+1)[1]
assert 67000000<e0*B*(l-1)/h**2<e1*B*(h-1)/l**2<68000000
print('endpoint verified')
