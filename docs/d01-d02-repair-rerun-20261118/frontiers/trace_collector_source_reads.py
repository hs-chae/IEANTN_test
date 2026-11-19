"""Read-only original collector dependency census; no scientific execution."""
from pathlib import Path
import sys
import os
import json
import hashlib
import collect

root=collect.O
study=root.parents[1]
seen=set()

def hook(event,args):
    if event!='open' or not args or not isinstance(args[0],(str,bytes,os.PathLike)):
        return
    p=Path(os.fsdecode(args[0]))
    if not p.is_absolute():
        p=Path.cwd()/p
    if not p.is_relative_to(study) or p.is_relative_to(root):
        return
    flags=args[2] if len(args)>2 and isinstance(args[2],int) else 0
    if not flags & (os.O_WRONLY|os.O_RDWR):
        seen.add(str(p))

def read_only_save(name,value):
    produced=(json.dumps(value,indent=2,ensure_ascii=False)+'\n').encode()
    if produced!=(root/name).read_bytes():
        raise ValueError('READ_CLOSURE_COLLECTOR_CHANGED_FROZEN_CURRENT_SOURCE_DATA')

sys.addaudithook(hook)
collect.save=read_only_save
collect.main()
mapfile=root.parent/'public-evidence-package-preparation-v1/PUBLIC_SELECTED_ORIGINAL_SOURCE_MAP_DRAFT_V7.json'
mapped=json.loads(mapfile.read_text())['files']
missing=[]
for name in sorted(seen):
    p=Path(name)
    if not p.is_file() or p.suffix=='.pyc':
        continue
    if name not in mapped:
        missing.append({'path':name,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size,'archive_path':'evidence/study/'+str(p.relative_to(study)),'role':'exact original metadata read dependency of current full11411 collector'})
record={'status':'READ_ONLY_ORIGINAL_COLLECTOR_COMPLETE_BYTE_IDENTICAL_DATA_WITH_ACTUAL_OPEN_DEPENDENCY_CENSUS','current_collector_sha256':hashlib.sha256((root/'collect.py').read_bytes()).hexdigest(),'current_source_data_sha256':hashlib.sha256((root/'ALL24_SOURCE_BOUND_OBJECTS.json').read_bytes()).hexdigest(),'external_original_reads':len(seen),'actual_read_paths':sorted(seen),'missing_from_draft_map':missing,'map':str(mapfile),'new_scientific_execution':False}
(root/'ACTUAL_COLLECTOR_SOURCE_READ_CLOSURE_V1.json').write_text(json.dumps(record,indent=2)+'\n')
print('READ_CLOSURE_MISSING',len(missing))
print('\n'.join(x['path']for x in missing))
