#!/usr/bin/env python3
"""Preserve concise accepted evidence and frozen sources, without compilation caches."""
from pathlib import Path
import argparse,hashlib,json,shutil
B=Path(__file__).resolve().parent
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--data',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();D=a.data.resolve();O=a.out.resolve()
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
need(not O.exists(),'fresh evidence output');need(D.name=='parabolic','explicit experiment-owned data root');need(json.loads((D/'clog-final-current-v2/RESULT.json').read_text())['status']=='PASS','final source replay accepted');need(json.loads((D/'clog-validator-controls-v2/RESULT.json').read_text())['status']=='PASS','final optimized validators accepted');O.mkdir(parents=True);selected=['canonical-replay-v1','octic-canonical-v1','clog-final-current-v2','clog-validator-controls-v2','clog-reproducer-cli-controls-v2'];rows=[]
for name in selected:
 root=D/name
 for src in sorted(root.rglob('*')):
  if not src.is_file():continue
  rel=src.relative_to(root)
  if any(part in {'objects','__pycache__'}for part in rel.parts):continue
  if src.suffix in {'.olean','.ilean','.ir','.o','.pyc'}:continue
  dst=O/name/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);rows.append({'file':str(dst.relative_to(O)),'sha256':sha(dst),'bytes':dst.stat().st_size})
for name in ['DEPENDENCY_IDENTITY.json','PORTABLE_GENERIC_CONTEXT.json','C_LOG_MOMENT_EXACT_DISPLAY.json','NUMERICAL_FAILURE_NOTES.md','REPRODUCER_FAILURES.md']:
 src=D/name
 if src.exists():shutil.copyfile(src,O/name);rows.append({'file':name,'sha256':sha(O/name),'bytes':(O/name).stat().st_size})
record={'status':'PRESERVED_ACCEPTED_SOURCE_AND_RECEIPT_EVIDENCE','files':rows,'bytes':sum(r['bytes']for r in rows),'excluded':'Only regenerable compiled application objects/caches. No source, accepted receipt, exact output, native binary association, frozen source, or failure log was removed from the data directory.','historical_results':'unchanged','no_experiment_data_deleted':True};(O/'MANIFEST.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps({'status':record['status'],'files':len(rows),'bytes':record['bytes']},indent=2))
