
#!/usr/bin/python3.10
'''Read sieve.c output on stdin and certify sharp Mertens onset brackets.
Usage: /work/mertens-check | PYTHONDONTWRITEBYTECODE=1 /usr/bin/python3.10 endpoints.py'''
import sys
from fractions import Fraction as F
from check import I, rng, log, exp, less

def process(txt):
    end={}
    for row in txt.splitlines():
        w=row.split()
        if w and w[0]=='anchor':
            p,q=map(int,w[1:3]); z=list(map(int,w[3:]))
            assert len(z)==6 and all(z[2*j]<=z[2*j+1] for j in range(3))
            assert (p,q) not in end
            end[p,q]=[rng(F(z[2*j],2**60),F(z[2*j+1],2**60)) for j in range(3)]
    assert set(end)=={(2278379,2278421),(912559,912581)}
    assert 'finite Mertens certificate passed; N=100000000, prime count=5761455' in txt
    r0,r1,_=end[2278379,2278421]
    _,_,r2=end[912559,912581]
    A=exp(r0)
    l=log(2278379)
    less(2*A,3*l)
    less(3*(r1-log(l)),1)
    l=log(912559)
    less(2*(r2-l),l)
    def cQ(t): l=log(t); return (A-l)*l*l
    def c1(t): l=log(t); return (r1-log(l))*l**3
    def c2(t): l=log(t); return (r2-l)*l*l
    for c,p,q,y in [
        (cQ,'2278381.71','2278381.72','.2'),
        (c1,'2278382.10','2278382.20','.2'),
        (c2,'912559.98','912560.00','.3')]:
        less(y,c(p)); less(c(q),y)
        print('sharp last root lies in ('+p+','+q+')')
    less(cQ('2278381.78'),'.199995')
    less(c1('2278382.30'),'.19999')
    less(c2('912565'),'.299')

if __name__=='__main__': process(sys.stdin.read())
