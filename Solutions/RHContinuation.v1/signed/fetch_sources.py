#!/usr/bin/env python3
"""Regenerate the primary PDF research cache, accepting only pinned SHA256 bytes."""
from pathlib import Path
import argparse,json,urllib.request,hashlib,time
B=Path(__file__).resolve().parent
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);p.add_argument('--check-cache',type=Path);a=p.parse_args()
if a.out.exists():raise ValueError('fresh output required')
pins=[json.loads((B/name).read_text())for name in ['NICOLAS_SOURCE_PIN.json','BFKNW_PIN.json']]+json.loads((B/'mobius/PRIMARY_SOURCE_PINS.json').read_text())
if len({r['sha256']for r in pins})!=len(pins):raise ValueError('duplicate source pin')
rows=[];a.out.mkdir(parents=True);started=time.monotonic()
for i,r in enumerate(pins):
 if a.check_cache:
  matches=[p for p in a.check_cache.rglob('*.pdf')if hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256']]
  if not matches:raise ValueError('pinned source absent in checked cache:'+r['url'])
  raw=matches[0].read_bytes();origin=str(matches[0])
 else:
  raw=urllib.request.urlopen(r['url'],timeout=20).read();origin=r['url']
 if len(raw)!=r['bytes']or hashlib.sha256(raw).hexdigest()!=r['sha256']:raise ValueError('primary source bytes changed:'+r['url'])
 target=a.out/(f'{i:02d}-'+r['sha256'][:12]+'.pdf');target.write_bytes(raw);rows.append({'url':r['url'],'path':target.name,'sha256':r['sha256'],'bytes':len(raw),'checked_origin':origin})
receipt={'status':'PASS_ALL_PRIMARY_PDF_IDENTITIES','count':len(rows),'mode':'local-cache-byte-reproduction'if a.check_cache else'fresh-public-download','source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'elapsed_seconds':time.monotonic()-started,'sources':rows}
tmp=a.out/'RESULT.json.tmp';tmp.write_text(json.dumps(receipt,indent=2)+'\n');tmp.replace(a.out/'RESULT.json');print(receipt['status'],len(rows))
