"""Check joins and explicitly displayed numerical comparisons in the finite summaries."""
import re
from pathlib import Path
from rigor import I, exp, F
def read(name,N):
    s=Path(name).read_text().splitlines()
    assert s[1].startswith(f"N={N},")
    bands=[]
    onsets={}
    for ln in s[2:]:
        m=re.fullmatch(r"\[(\d+),(\d+)\] : (\d+) (\d+) (\d+)",ln)
        if m: bands.append(tuple(map(int,m.groups())))
        if re.fullmatch(r"\d+ : \d+ \d+ \d+",ln):
            i,a,b,c=map(int,ln.replace(":","").split())
            onsets[i]=(a,b,c)
    assert bands[0][0]==300000 and bands[-1][1]==N
    assert all(x[0]<x[1] for x in bands)
    assert all(x[1]==y[0] for x,y in zip(bands,bands[1:]))
    assert set(onsets)==set(range(1,31))
    return bands,onsets
def cap(bands,a,b):
    return tuple(max(x[j] for x in bands if x[1]>a and x[0]<b) for j in (2,3,4))
if __name__=='__main__':
    short,o1=read("finite100m.txt",10**8)
    mid,o2=read("finite20b.txt",2*10**10)
    full,o3=read("finite26.txt",195729609429)
    assert exp(I('18.8'))<150000000
    assert max(cap(short,5*10**7,10**8))<61000000
    assert max(cap(mid,10**8,150000000))<61000000
    assert o2[1]==(10099524684,10099524684,10148219812)
    assert o2[2][-1]==max(o2[2])==1133202783
    assert o1[7][-1]==40890944 and o1[9][:2]==(18337513,18337513)
    assert cap(mid,2278382,2*10**10)[0]==199972897
    assert cap(mid,2278383,2*10**10)[1]==199928568
    assert cap(mid,912560,2*10**10)[2]==299999703
    assert exp(26)<195729609429 and exp(F('23.7'))<2*10**10
    print('Finite coefficient summaries and joins checked.')
