#!/usr/bin/env python3
"""Restore own original historical flat filenames into a fresh writable folder."""
from pathlib import Path
import argparse,hashlib,json
p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);a=p.parse_args();root=Path(__file__).resolve().parent
j=json.loads((root/'OWN_HISTORY_INDEX.json').read_text())
if a.out.exists():raise ValueError('fresh output directory required')
a.out.mkdir(parents=True)
for stage in ['D01','D02']:
 d=a.out/stage;d.mkdir()
 for row in j['stages'][stage]['payloads']:
  source=root/row['packet_name'];name=row['original_name'];raw=source.read_bytes()
  if Path(name).name!=name or hashlib.sha256(raw).hexdigest()!=row['sha256']:raise ValueError('historical source identity differs')
  (d/name).write_bytes(raw)
print('Restored exact own original filenames; no program or proof was executed.')
