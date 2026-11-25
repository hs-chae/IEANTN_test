from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent
a=[dict(path=q.name,sha256=hashlib.sha256(q.read_bytes()).hexdigest()) for q in sorted(p.iterdir()) if q.name not in ('LOCK.json','.LOCK.tmp') ]
assert len(a)<=15 and all((p/e['path']).is_file() and not (p/e['path']).is_symlink() and (p/e['path']).stat().st_size<=2**21 for e in a)
tmp=p/'.LOCK.tmp'
tmp.write_text(json.dumps(dict(files=a),indent=2)+'\n')
tmp.replace(p/'LOCK.json')
