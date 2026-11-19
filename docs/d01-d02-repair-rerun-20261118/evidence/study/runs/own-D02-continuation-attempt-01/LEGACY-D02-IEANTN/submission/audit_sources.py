"""Read only bound packet files and full pinned PDF/text objects."""
from pathlib import Path
from hashlib import sha256
import re,json
S=Path('/work/submission')
P=Path('/task')
C=Path('/corpus/originals')
for r in json.loads((P/'SOURCE_INDEX.json').read_text())['sources']:
    for k in ('pdf','text'):
        p=C/r[k]
        o=p.read_bytes()
        h=sha256(o).hexdigest()
        assert h==r[k+'_sha256'],p
        print(r['source_id'],k,h,len(o),flush=True)
    ls=o.decode().splitlines()
    # Page and physical LF extraction landmarks, with unambiguous page offsets.
    lf=o.decode().split('\n')
    page=1
    for n,l in enumerate(lf,1):
        m=re.search(r'=+ (?:ORIGINAL )?PDF PAGE (\d+) =+',l)
        if m:page=int(m.group(1))
        if re.match(r'^(?:Theorem|Corollary|Lemma|Proposition|Remark|Table|APPENDIX) ',l):
            print(' ',page,n,l[:130])
for r in json.loads((P/'OWN_SOURCE_INDEX.json').read_text())['payloads']:
    name=r['packet_name']
    expected=r['sha256']
    assert sha256((P/name).read_bytes()).hexdigest()==expected
    if name not in ('STAGE_STATUS.json','LOCK.json'):
        assert sha256((S/name).read_bytes()).hexdigest()==expected
print('Archived own-source digests verified.')
