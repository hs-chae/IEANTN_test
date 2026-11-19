#!/usr/bin/python3.10
from repair_ram import *
from ram_early import los

def proof(m,c):
    s=Q('49.1')
    # Use a conservative spectral-only tail at 240, as in cert.py.
    tail(Q(240),27,m,[1,14,c],False)
    margin=I(145-c)
    def model(u):
        return margin/I(u)**2+sum(I(g(k))/I(u)**(k-4) for k in range(7,28))
    mins=[]
    for l,r,base in [(s,Q('49.4'),Q(1,64)),(Q('49.4'),Q(58),Q(1,4)),(Q(58),Q(240),Q(1,4))]:
        mn=D('Infinity')
        def block(a,b):
            nonlocal mn
            bound=los(a,b,False) if r<=58 else loss(a,b,m,False)
            q=(model(b)-bound).a
            if q>0:
                mn=min(q,mn)
                return
            if b-a<=Q(1,1024):
                raise ValueError((a,b,q))
            mid=(a+b)/2
            block(a,mid);block(mid,b)
        while l<r:
            u=min(l+base,r)
            block(l,u)
            l=u
        mins.append(mn)
    print('fixed L>=49.1',m,str(c),'slacks',*[f'{x:.8E}' for x in mins],flush=True)

if __name__=='__main__':
    import sys
    if len(sys.argv)==3: proof(int(sys.argv[1]),Q(sys.argv[2]))
    else:
        for m,c in [(0,Q('7.5')),(1,Q('79.9'))]: proof(m,c)
