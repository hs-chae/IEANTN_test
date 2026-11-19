"""Read raw PDF glyph placements where supplied extraction is suspect."""
import re,zlib,hashlib
from pathlib import Path
root=Path('/corpus/originals')
def stream(base,obj):
    b=(root/(base+'.pdf')).read_bytes()
    m=re.search(rb'(?m)^'+str(obj).encode()+rb' 0 obj.*?stream\r?\n(.*?)\r?\nendstream',b,re.S)
    s=zlib.decompress(m[1])
    print(base,obj,hashlib.sha256(b).hexdigest(),hashlib.sha256(s).hexdigest())
    return s.decode('latin1')
s=stream('PlattTrudgianFiniteRH',114)
i=next(m.start() for m in re.finditer(r'\(2\)[-0-9.]+\(6\)[-0-9.]+\(5\)[-0-9.]+\(7\)',s))
j=s.rfind('[(lo)',0,i)
print('Pi formula just before its domain 2657:',repr(s[j:i+62]))
s=stream('FKS',264)
for m in re.finditer(r'\(1\)',s):
    c=s[max(0,m.start()-700):m.start()+42]
    if re.search(r'\(\x15\)|\(\x14\)',c) and ('0.236' in c or r'(0)' in c):
        print('Theorem 2.7 glyph context',repr(c))
s=stream('FKS',706)
for l in s.splitlines():
    # Table body is positioned in fixed-width row-aligned columns. TJ
    # displacements less than -500 split decimal columns.
    if 'TJ' not in l:continue
    cells=[''.join(re.findall(r'\(([0-9.]+)\)',g)) for g in re.split(r'-(?:[5-9]\d\d|\d{4,})\.\d+',l)]
    if cells[0] in ('.75','0.75','0.80','0.81','0.82','0.83','0.84','0.85','0.86','0.87'):
        print('Table 8 row',cells)
