#!/usr/bin/env python3
"""Package exact public source/evidence with content deduplication."""
from pathlib import Path
import argparse,hashlib,json,zipfile
R=Path(__file__).resolve().parents[1];S=R/'network/Solutions/RHExposureStudy.v1'
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);a=p.parse_args();out=a.out.resolve()
if out.exists():raise ValueError('fresh archive destination')
external={r['path']for r in json.loads((S/'ledgers/EXTERNAL_SOURCE_DOCUMENTS.json').read_text())['documents']}
rows=[];objects={}
for f in sorted(S.rglob('*')):
 if f.is_symlink():raise ValueError('unexpected publication symlink:'+str(f))
 if not f.is_file():continue
 if f.relative_to(S).as_posix()in external:continue
 if '__pycache__'in f.parts or f.suffix in ['.olean','.o','.so','.a','.pyc']:raise ValueError('regenerable compiled cache in publication:'+str(f))
 raw=f.read_bytes();h=hashlib.sha256(raw).hexdigest();rows.append({'path':f.relative_to(S).as_posix(),'bytes':len(raw),'sha256':h});objects[h]=raw
restore=(S/'scripts/restore_evidence_bundle.py').read_bytes();manifest={'schema':'RH_CONTENT_ADDRESSED_EVIDENCE_V1','files':rows,'restore_sha256':hashlib.sha256(restore).hexdigest(),'source_baseline_commit':'97c2f6bf91b8ac1eff6a298557c05e25aa1a97bf','neutral_checkpoint_commit':'d5e89350283e42a0c1b1c323fd18c8a41ec6937d','mathematical_status':'See ledgers/RESULTS.json; no stronger status inferred from archive integrity','exact_reproducibility':'Restore tree then README.md; no raw credentials or coordinator conversations packaged'}
with zipfile.ZipFile(out,'w',zipfile.ZIP_DEFLATED,compresslevel=9)as z:
 z.writestr('MANIFEST.json',json.dumps(manifest,indent=2)+'\n');z.writestr('RESTORE.py',restore);z.writestr('README.txt','Run: python RESTORE.py <this ZIP> --out /absolute/fresh/study\nThen read study/README.md. Physical objects/ are deduplicated bytes, not a partial source checkout.\n')
 for h,raw in sorted(objects.items()):z.writestr('objects/'+h,raw)
receipt={'archive':str(out),'sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'bytes':out.stat().st_size,'logical_files':len(rows),'logical_bytes':sum(r['bytes']for r in rows),'unique_objects':len(objects),'deduplicated_uncompressed_bytes':sum(map(len,objects.values()))};out.with_suffix('.receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
