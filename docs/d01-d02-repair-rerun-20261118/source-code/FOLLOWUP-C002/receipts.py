"""Exact Decimal comparisons of saved outward run receipts with selected claims."""
from pathlib import Path
from decimal import Decimal as D
p=Path(__file__).resolve().parent
def load(filename,marker):
    out={}
    for l in (p/filename).read_text().splitlines():
        if l.startswith(marker+' '):
            v=l.split()[len(marker.split()):]
            out[D(v[0])]=tuple(map(D,v[1:]))
    return out
def check(rs,onset,*cut):
    a=rs[D(onset)]
    assert len(a)==len(cut)
    assert all(x<D(y) for x,y in zip(a,cut))
s=load('smallprod.log','extended scaled upper')
w=load('weighted.log','weighted scaled upper')
e=load('early.log','early scaled maxima upper')
for x,cl in [('2',('3.826','3.960','3.971','4.551')),
             ('1000',('2.247','2.261','2.271','2.570')),
             ('10000',('1.266','1.268','1.271','1.414')),
             ('100000',('.596','.596','.597','.656')),
             ('500000',('.343','.343','.343','.372')),
             ('900000',('.288','.288','.288','.313')),
             ('1000000',('.275','.275','.276','.298'))]:
    check(e,x,*cl)
for x,c in [('2000000','.209'),('2278382.2','.2'),('2278383','.19992'),
            ('3000000','.19844'),('5000000','.15013'),('10000000','.120')]:
    check(s,x,c,c,c)
for x,c in [('2278381.8','.2'),('2278381.9','.19999'),('2278382','.19998')]:
    assert all(m<D(c) for m in s[D(x)][:2])
for x,c in [('912000','.30151'),('912559.998','.3'),('912560','.2999995'),
            ('1000000','.296'),('2000000','.2248'),('3000000','.212'),
            ('5000000','.162'),('10000000','.130')]:
    check(w,x,c)
assert '2473381581 primes checked' in (p/'bridge.log').read_text()
print('Selected claim tables and exact finite receipts agree')
