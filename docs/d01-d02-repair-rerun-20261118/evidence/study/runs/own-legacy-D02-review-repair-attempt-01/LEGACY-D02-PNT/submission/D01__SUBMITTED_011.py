import hashlib,json,os
from pathlib import Path
d=Path(__file__).resolve().parent
files=[]
for f in sorted(d.iterdir()):
    if f.is_dir() or f.name in ('LOCK.json','.LOCK.tmp'): continue
    assert f.is_file() and not f.is_symlink() and f.stat().st_size <= 2**21
    files.append(dict(path=f.name,sha256=hashlib.sha256(f.read_bytes()).hexdigest()))
assert len(files)<=15
p=d/'.LOCK.tmp'
p.write_text(json.dumps(dict(files=files),separators=(',',':'))+'\n')
os.replace(p,d/'LOCK.json')
