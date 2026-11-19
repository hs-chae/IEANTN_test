"""Retrieve targeted PDF content operators for layout/typography readback."""
import hashlib, re, zlib
from pathlib import Path

base=Path('/corpus/originals')
def stream(paper,obj):
    pdf=(base/paper).read_bytes()
    m=re.search(fr'(?m)^{obj} 0 obj\b(.*?)\bstream\r?\n'.encode(),pdf,re.S)
    assert m and b'/FlateDecode' in m.group(1)
    raw=zlib.decompress(pdf[m.end():])
    print(paper,'stream object',obj,'uncompressed sha256',hashlib.sha256(raw).hexdigest())
    return raw.decode('latin1')

def relevant(paper,obj,label,preceding):
    d=stream(paper,obj).split('\n')
    i=next(i for i,line in enumerate(d) if label in line)
    for j in range(i-preceding,i+1): print(j,ascii(d[j]))

relevant('CH2.pdf',623,r'\0509.1\051',14)
relevant('CH2.pdf',640,r'\0509.4\051',25)
d=stream('FKS.pdf',264).split('\n')
for j in range(380,408): print(j,ascii(d[j]))
