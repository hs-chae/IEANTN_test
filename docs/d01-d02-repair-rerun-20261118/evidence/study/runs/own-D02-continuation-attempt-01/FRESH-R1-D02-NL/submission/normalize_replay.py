"""Bound original-source audit and quick independent replay of inherited constant inputs."""
from pathlib import Path
import hashlib,json,subprocess,sys
from mcert import constants
for s in json.loads(Path('SOURCE_INDEX.json').read_text())['sources']:
 for t in ('pdf','text'):
  path=Path('/corpus/originals',s[t]);data=path.read_bytes()
  assert hashlib.sha256(data).hexdigest()==s[t+'_sha256']
  if t=='text':print(s['source_id'],len(data),'hashed pinned extraction',flush=True)
constants()
s=Path('mertens.cc').read_text()
i=s.index('    for(unsigned p=2;p<=N;++p){')
generated=s[:i].replace('N=250000000, N0=10000000','N=10000000, N0=10000000')+'    return 0;\n}\n'
cmd=['/usr/bin/g++','-O3','-std=c++17','-x','c++','-','-o','/work/norm2']
subprocess.run(cmd, input=generated, text=True, check=True)
a=subprocess.check_output(['/work/norm2'],text=True)
assert a.splitlines()==Path('mertens.out').read_text().splitlines()[:2]
print(a,end='')
