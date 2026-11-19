from pathlib import Path
from hashlib import sha256
import re,zlib
def streams(name,page):
    data=Path('/corpus/originals',name+'.pdf').read_bytes()
    objs=dict((int(a), b) for a,b in re.findall(rb'(?ms)^(\d+) 0 obj\s(.*?)endobj',data))
    ref=lambda s,k:int(re.search(rb'/'+k+rb'\s*(\d+) 0 R',s)[1])
    root=int(re.findall(rb'/Root\s*(\d+) 0 R', data)[-1])
    def walk(i):
        d=objs[i]
        if re.search(rb'/Type\s*/Page\b',d):yield i;return
        for j in re.findall(rb'(\d+) 0 R',re.search(rb'/Kids\s*\[([^\]]+)',d)[1]):
            yield from walk(int(j))
    p=list(walk(ref(objs[root],b'Pages')))[page-1]
    o=ref(objs[p],b'Contents'); b=objs[o]; s=re.split(rb'stream\r?\n',b,maxsplit=1)[1]
    return p,o,zlib.decompress(s) if b'/FlateDecode' in b else s.split(b'endstream')[0]
if __name__=='__main__':
  for n,p,keys in [('CH2',35,[rb'1423',rb'110102617',rb'75858',rb'787',rb'9.1']),('CH2',3,[rb'260.267 515.138',rb'260.267 503.948',rb'[(coth)]']),('FKS',7,[rb'Corollary',rb'optimized']),('FKS',26,[rb'computed',rb'optimized'])]:
    obj,co,r=streams(n,p)
    print(n,p,obj,co,sha256(r).hexdigest())
    for key in keys:
      i=r.find(key)
      if i>=0: print(repr(r[max(0,i-300):i+300]))
