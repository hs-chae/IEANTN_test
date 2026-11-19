import json,hashlib
from pathlib import Path
idx=json.loads(Path('/task/SOURCE_INDEX.json').read_text())
paths=json.loads(Path('/task/RUNTIME_PATHS.json').read_text())
root=Path(paths['paper_root'])
assert root==Path(idx['root'])
for rec in idx['sources']:
    for kind in ('pdf','text'):
        p=root/rec[kind]
        b=p.read_bytes()
        h=hashlib.sha256(b).hexdigest()
        assert h==rec[kind+'_sha256']
        print(rec['source_id'],p.name,len(b),h)
