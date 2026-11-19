"""Local identity/lock validation; not the external readiness gate."""
from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent
packet=Path('/task')
def sha(b):return hashlib.sha256(b).hexdigest()
index={r['packet_name']:r for r in json.loads((packet/'CANDIDATE_INDEX.json').read_text())['candidate_files']}
lock=json.loads((p/'LOCK.json').read_text())
assert set(lock)=={'files'}
assert sorted(r['path'] for r in lock['files'])==sorted(q.name for q in p.iterdir() if q.name!='LOCK.json')
for r in lock['files']:
 q=p/r['path']
 assert q.is_file() and not q.is_symlink() and sha(q.read_bytes())==r['sha256']
d=json.loads((p/'review.json').read_text())
assert d['assessment_complete'] is True and d['all_claims_inventoried'] is True
for c in d['claims']:
 assert c['M_status'] not in ('unassessed','review_interrupted')
 w=c['written_source']
 start,*tail=map(int,c['written_source_passage'].split('-'))
 assert start<=w['physical_LF']<=(tail or [start])[0]
 assert c['written_source_restored_basename']==index[w['file']]['original_name']
 for r in [w,*c['implemented_formula_readbacks']]:
  assert set(r)=={'file','physical_LF','sha256'}
  b=(packet/r['file']).read_bytes()
  assert sha(b)==r['sha256']==index[r['file']]['sha256']
  n=r['physical_LF']; lines=b.split(b'\n')
  assert type(n) is int and 1<=n<=len(lines) and lines[n-1].strip()
print(f"{len(d['claims'])} complete claim records; exact single-line source identities, implemented locators, and {len(lock['files'])} payload hashes verified")
