"""PDF placement readback for the crucial finite-height formula (no renderer needed)."""
from pathlib import Path
from hashlib import sha256
import re,zlib
p=Path('/corpus/originals/PlattTrudgianFiniteRH.pdf')
d=p.read_bytes()
def obj(i):
    return re.search(rb'(?m)^'+str(i).encode()+rb' 0 obj\b',d)
assert b'/Kids [\n4 0 R\n52 0 R\n81 0 R\n112 0 R' in d
assert b'/Contents 114 0 R' in d[obj(112).start():].split(b'endobj',1)[0]
raw=d[obj(114).start():].split(b'endobj',1)[0]
stream=zlib.decompress(re.split(rb'stream\r?\n',raw,maxsplit=1)[1])
i=stream.index(rb'[(li\()-1.42337]TJ',7600)
j=stream.index(rb'[(\()-1.42541(2)-2.83652(6)-2.83857(5)-2.83857(7)',i)
proof=stream[i:j+80]
assert b'251.76 506.52 Tm' in proof and b'12.1199 8.16016 Td' in proof
assert b'/R31 7.97011 Tf\n15.1199 5.16016 Td\n[(2)' in proof
print('PDF',sha256(d).hexdigest(),'page4 object112 stream114',sha256(stream).hexdigest())
print('In the pi line, fraction bar centered near y=517.9, 8pi below at y=506.52, log main glyphs at y=514.68016 and superscript 2 at y=519.84032. The trailing x is on the log baseline; log squared is not in the denominator.')
for line in proof.splitlines():
    print(line.decode('ascii','backslashreplace').encode('unicode_escape').decode())
