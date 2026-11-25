'''Exact all-real inverse Fourier bounds for rational steps; no FFT or float.'''
from fractions import Fraction as Q
from math import lcm
import sys,json
from gauss_cert import PI,fl,print_interval
S=10**36

def ceildiv(n,d):return -(-n//d)

def sin_table(M):
    # Return centers z_i with |sin(2*pi*i/M)-z_i/S| <= 64/S.
    assert M%4==0
    pil,pih=PI
    lo=fl(pil*S);hi=ceildiv((pih*S).numerator,(pih*S).denominator)
    z=[]
    for i in range(M//4+1):
        n=(2*i*lo)//M; h=ceildiv(2*i*hi,M)
        l=n
        a,b=l,h
        for k in range(1,40):
            c=S*S*(2*k)*(2*k+1)
            l=l*n*n//c;h=ceildiv(h*(ceildiv(2*i*hi,M))**2,c)
            if k%2:a-=h;b-=l
            else:a+=l;b+=h
        # |next term| <= (pi/2)^81/81! < 1/S.
        c=S*S*80*81
        assert ceildiv(h*(ceildiv(2*i*hi,M))**2,c)<=1
        a-=1;b+=1
        assert b-a<=128
        z.append((a+b)//2)
    return z+[z[M//2-i] for i in range(M//4+1,M//2)]+[-z[0]]+[-z[min(i,M//2-i)] for i in range(1,M//2)]

def read(path):
    d=json.load(open(path))
    m=d['m']
    if 'H' in d:
        H,den=d['H'],d['den']
    else:
        a=[Q(1)]*m+[Q(v) for v in d['wing_heights']]
        den=lcm(*(q.denominator for q in a));H=[int(v*den) for v in a]
    assert all(isinstance(x,int) for x in H) and isinstance(den,int) and den>0
    assert 0<m<len(H) and H[:m]==[den]*m and max(H)<=den
    A=max(Q(1),1-Q(min(H),den))
    return m,H,den,A,d

def main(path,G):
    m,H,den,A,d=read(path)
    z=sin_table(2*G)
    jumps=[a-b for a,b in zip(H,H[1:]+[0])]
    err=64*sum(map(abs,jumps))
    NZ=[(j+1,a) for j,a in enumerate(jumps) if a]
    pilo=Q(fl(PI[0]*10**36),10**36)
    best_n,best_k,kbest=0,1,0
    for k in range(1,G+1):
        n=abs(sum(a*z[(j*k)%(2*G)] for j,a in NZ))+err
        if n*best_k>best_n*k:best_n,best_k,kbest=n,k,k
    best=max(Q(abs(2*sum(H)),m*den),Q(best_n*2*G,S*den*m*best_k)/pilo)
    I=sum(abs(h)*((j+1)**3-j**3) for j,h in enumerate(H))
    delta=Q(10*I,3*den*m**3)*Q(m,2*G)**2
    M=best+delta
    print(path,'feasible A',A,'k/G',kbest,G)
    print_interval('sample cap',(best,best),12)
    print_interval('global cap',(M,M),12)
    if 'target' in d:assert M<Q(d['target'])
    if 'sup_upper_bound' in d:assert M<Q(d['sup_upper_bound'])
    return M

if __name__=='__main__': main(sys.argv[1],int(sys.argv[2]))
