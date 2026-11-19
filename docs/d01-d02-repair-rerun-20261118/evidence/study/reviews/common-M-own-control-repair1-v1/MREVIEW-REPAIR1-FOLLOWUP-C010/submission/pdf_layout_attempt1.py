#!/usr/bin/python3.10
"""Read exact vector typesetting commands from the two ambiguous original pages."""
import re, zlib, hashlib
from pathlib import Path
root=Path('/corpus/originals')
def page(filename,number):
    b=(root/filename).read_bytes()
    def obj(n):
        return re.search(rb'(?:^|\n)'+str(n).encode()+rb' 0 obj\s*(.*?)endobj',b,re.S)[1]
    kids=re.search(rb'/Kids\s*\[(.*?)\]',obj(3),re.S)[1]
    pn=int(re.findall(rb'(\d+)\s+0 R',kids)[number-1])
    stream=int(re.search(rb'/Contents\s+(\d+)\s+0 R',obj(pn))[1])
    q=zlib.decompress(re.split(rb'\bstream\r?\n',obj(stream),maxsplit=1)[1])
    print(filename, hashlib.sha256(b).hexdigest(), 'page',number,'page object',pn,'stream object',stream)
    return q.split(b'\n')
pt=page('PlattTrudgian1809.03134v2.pdf',10)
for start in (1266,1468):
    ls=pt[start:start+10]
    assert ls[0].startswith(b'[(7)')
    assert ls[3].startswith(b'[(\x01)')
    assert ls[6].startswith(b'[(2)')
    assert ls[7].startswith(b'/R45 7.97011')
    assert float(ls[8].split()[1])>4
    assert ls[9].startswith(b'[(8)')
    print('Raised 8 after numeral 2 (the term is 7 times 2^8):')
    for j,l in enumerate(ls,start): print(j,repr(l))
fks=page('FKS.pdf',7)
assert b'(\x0e)' in fks[383] and b'(\x15)' in fks[386] and b'(1)' in fks[389]
print('Printed delta >= 1, one baseline no raised or lowered continuation before comma:')
for j in range(381,393): print(j,repr(fks[j]))
