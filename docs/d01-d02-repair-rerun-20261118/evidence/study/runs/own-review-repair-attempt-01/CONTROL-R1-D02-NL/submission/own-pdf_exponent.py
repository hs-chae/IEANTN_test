"""Direct pinned PDF inspection supplement (stdlib only).
Content 114 is the /Contents of page object 112, fourth in the /Kids array.
The exponent glyph belongs to the reduced font R31 above each log baseline.
"""
from pathlib import Path
import re,zlib
p=Path('/corpus/originals/PlattTrudgianFiniteRH.pdf').read_bytes()
assert re.search(rb'3 0 obj\s*<< /Type /Pages /Kids \[\s*4 0 R\s*52 0 R\s*81 0 R\s*112 0 R',p)
assert re.search(rb'112 0 obj\s*<</Type/Page.*?/Contents 114 0 R',p,re.S)
o=re.search(rb'\n114 0 obj.*?stream\r?\n',p,re.S)
t=zlib.decompress(p[o.end():]).decode('latin1').splitlines()
for i in range(349,447): print(i,t[i].encode('unicode_escape').decode('ascii'))
assert '[('+chr(2+48)+')4.03117]TJ'==t[420]
