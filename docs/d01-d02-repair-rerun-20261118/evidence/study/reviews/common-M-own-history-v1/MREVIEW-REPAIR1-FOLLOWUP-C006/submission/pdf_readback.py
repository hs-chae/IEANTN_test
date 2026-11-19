"""Raw original PDF page-content readback (for symbol/layout audit)."""
import re,sys,zlib
from pathlib import Path
def stream(v):
    m=re.search(rb'\bstream\r?\n|\bstream\r',v)
    if not m:return v
    raw=v[m.end():].rsplit(b'endstream',1)[0]
    return zlib.decompress(raw) if b'/FlateDecode' in v[:m.start()] else raw
def get(pdf,n):
    b=Path(pdf).read_bytes()
    obj={int(m[1]):m[2] for m in re.finditer(rb'(?:^|[\r\n])(\d+) 0 obj\s*(.*?)\s*endobj',b,re.S)}
    for k,v in list(obj.items()):
        if re.search(rb'/Type\s*/ObjStm',v):
            d=stream(v)
            first=int(re.search(rb'/First\s+(\d+)',v)[1]); pairs=list(map(int,d[:first].split()))
            for j in range(0,len(pairs),2):
                a=first+pairs[j+1]; b=first+pairs[j+3] if j+3<len(pairs) else len(d)
                obj[pairs[j]]=d[a:b]
    pages=[(k,v) for k,v in obj.items() if re.search(rb'/Type\s*/Page\b',v)]
    if 'OpenAIQRH' in pdf or 'Dusart' in pdf:
        root=next(v for v in obj.values() if re.search(rb'/Type\s*/Catalog\b',v))
        def walk(k):
            v=obj[k]
            if re.search(rb'/Type\s*/Page\b',v):yield k,v
            else:
                for z in re.findall(rb'(\d+) 0 R',re.search(rb'/Kids\s*\[(.*?)\]',v,re.S)[1]):
                    yield from walk(int(z))
        pages=list(walk(int(re.search(rb'/Pages\s*(\d+) 0 R',root)[1])))
    k,v=pages[n-1]
    ref=re.search(rb'/Contents\s*(\[.*?\]|\d+ 0 R)',v,re.S)[1]
    return k,v,[(int(c),stream(obj[int(c)])) for c in re.findall(rb'(\d+) 0 R',ref)],obj
if __name__=='__main__':
    k,v,c,o=get(sys.argv[1],int(sys.argv[2]))
    print(k,v)
    for r,s in c:print(r,s.decode('latin1'))
