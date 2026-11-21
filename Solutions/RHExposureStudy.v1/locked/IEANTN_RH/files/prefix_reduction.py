"""Count requested rows from the pinned manifest only; not count truth."""
from pathlib import Path
import json,hashlib
p=Path('/ieantn/Solutions/RamanujanSourcePV.v1/evidence/full-scalars-kernel-v1/PROPOSAL.json')
raw=p.read_bytes()
d=json.loads(raw)
rows=d['blocks']
if not (rows[0]['start']==d['begin'] and rows[-1]['stop']==d['stop']
        and sum(b['count'] for b in rows)==d['rows']
        and all(a['stop']==b['start'] for a,b in zip(rows,rows[1:]))):
    raise RuntimeError('not a manifest chain')
print('manifest SHA256',hashlib.sha256(raw).hexdigest())
for cut in [1490000000001,1250000000000,640000000000,610000000000]:
    low=sum(b['count'] for b in rows if b['stop']<=cut)
    high=sum(b['count'] for b in rows if b['start']<cut)
    stop=max(b['stop'] for b in rows if b['start']<cut)
    print('cut',cut,'number of rows required in [%d,%d], as stand-alone full-block prefix ends at %s; at most %d count-bound sites' % (low,high,stop,2*high))
    print('only manifest census, no new count evidence')
