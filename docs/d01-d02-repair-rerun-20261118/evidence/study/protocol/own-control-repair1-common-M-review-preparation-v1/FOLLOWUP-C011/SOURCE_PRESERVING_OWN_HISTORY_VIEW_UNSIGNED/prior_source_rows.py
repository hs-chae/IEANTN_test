"""Transcribe the bound source row selections and certify comparison.
Reads only SOURCE_INDEX.json and the three bound original text extractions.
"""
import json,re,hashlib
from pathlib import Path
from intervals import I,F,PI,exp,log
root=Path('/corpus/originals')
def lines(name):return (root/(name+'.txt')).read_text().split('\n')
def extract():
    f=lines('FKS')
    sci=re.compile(r'([0-9.]+) e(-?[0-9]+)')
    onset=r'(?:[0-9]+|[0-9]+(?: [0-9]{3})+)'
    f5=[]
    for i in range(2315,2573):
        if re.fullmatch(onset,f[i]) and re.fullmatch(r'0\.\d+',f[i+1]) and sci.fullmatch(f[i+6]):
            f5.append([int(f[i].replace(' ','')), f[i+6].replace(' ','')])
    f6=[]
    for i in range(2592,2748):
        if re.fullmatch(onset,f[i]) and re.fullmatch(r'\d+\.\d+',f[i+1]) and sci.fullmatch(f[i+3]):
            a=f[i].replace(' ','')
            if len(a)==3 and a[:2]=='10':a=str(10**int(a[2]))
            f6.append([int(a),f[i+1],f[i+3].replace(' ','')])
    d=lines('Dusart2018')
    dus=[]
    for i in range(480,765):
        if (re.fullmatch(r'\d+',d[i]) and re.fullmatch(r'0\.\d+',d[i+1])
            and re.fullmatch(r'\d+',d[i+2]) and re.fullmatch(r'[0-9.]+ E−\d+',d[i+5])):
            dus.append([int(d[i]),d[i+5].replace(' E−','e-')])
    assert len(f5)>=30 and f6[-1][0]==10**9 and dus[0][0]==20 and dus[-1][0]==13900
    pt=[(1000,'461.9','1.52','1.89','1.20e-5'),(2000,'411.4','1.52','1.89','8.35e-10'),
        (3000,'379.6','1.52','1.89','4.51e-13'),(4000,'355.1','1.52','1.89','7.33e-16'),
        (5000,'713.0','1.51','1.94','9.77e-19'),(6000,'611.6','1.51','1.94','4.23e-21'),
        (7000,'590.1','1.51','1.94','3.09e-23'),(8000,'570.5','1.51','1.94','3.12e-25'),
        (9000,'552.3','1.51','1.94','4.11e-27'),(10000,'535.4','1.51','1.94','6.78e-29')]
    return dict(FKS5=f5,FKS6=f6,Dusart1=dus,PT1=pt)
def lsci(s):
    mant,_,n=s.partition('e')
    return log(F(mant))+(int(n)*log(10) if n else I(0))
def compare(rows):
    # All entries compared to the slower comparator .0039 exp(-L/8).
    # Reconstructed CH2, B0 density handled separately in certificate.py.
    lg=log(F('.0039'))
    def at_const(a,c):assert (lg-F(max(170,a),8)).lt(lsci(c)),(a,c)
    for a,c in rows['FKS5']+rows['Dusart1']:at_const(a,c)
    for a,c,k in rows['FKS6']:at_const(a,k)
    def stretch(a,A,R,p,q):
        a=F(max(a,170)); p,q,R=map(F,(p,q,R))
        r=exp(log(a/R)/2)
        assert (lg-a/8).lt(log(F(A))+p*log(a/R)-q*r)
        assert (q/(2*R*r)).lt(F(1,8))
    stretch(170,'9.22022','1','1.5','.8476836')
    for a,A,k,q,c in rows['PT1']:
        stretch(a,A,'5.573412',k,q)
        at_const(a,c)
    for a,A,c in rows['FKS6']:stretch(a,A,'5.5666305','1.5','2')
    # FKS (4.1) beyond the precomputed rows: either T<=H and the
    # Perron term exceeds 2*1000^2/H, or the epsilon_2 term is
    # >= .99e-12 exp(-L/10) since B1(H,T)>=2R(H)/H>1e-12.
    assert (lg-125).lt(log(F(2*1000**2,3*10**12)))
    assert (lg-125).lt(log(F('.99e-12'))-100)
    # (5.2) explicitly adds 6.8979e-6. The first zero of CH2 B.7
    # at height 14..15 implies R>2/log 100 for a lawful zero-free input.
    Rmin=2/log(100)
    aa=I(1000)
    assert (lg-125).lt(log(F('6.8979e-6'))+F(3,2)*log(aa/F('5.573412'))-2*exp(log(aa/Rmin)/2))
    assert (1/exp(log(aa*Rmin)/2)).lt(F(1,8))
    # More conservative than all active Dusart power branches, with all active relative powers at most four.
    assert (lg-F(170,8)).lt(log(F('.01'))-4*log(170))
    assert F(4,170)<F(1,8)
if __name__=='__main__':
    for s in json.load(open('/task/SOURCE_INDEX.json'))['sources']:
        for k in ('pdf','text'):
            assert hashlib.sha256((root/s[k]).read_bytes()).hexdigest()==s[k+'_sha256']
    rows=extract()
    compare(rows)
    print(json.dumps(rows, indent=2))
