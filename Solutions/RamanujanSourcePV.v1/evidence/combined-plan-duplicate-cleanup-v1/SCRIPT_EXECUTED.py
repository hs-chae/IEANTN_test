#!/usr/bin/env python3
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import hashlib,json,os,stat,datetime
R=Path(__file__).resolve().parents[1];P=R/'research/primary-sources/COMBINED_CLEANUP_READONLY_PREVIEW.json';raw=P.read_bytes();expected='972c282ae463a85944a55e8a54f774c4025902bf03847944202f1b66a4e8fe0f'
if hashlib.sha256(raw).hexdigest()!=expected:raise ValueError('preview identity')
j=json.loads(raw);D=Path('/data/ivy-ramanujan-source-pv-20261119');base=D/'combined-clean-controls-v1';roots={base/'run-normal',base/'run-normal-final',base/'actual-allmode-controls/generated-O',base/'actual-allmode-controls/generated-OO'};out=R/'publication/combined-plan-duplicate-cleanup-v1';out.mkdir(exist_ok=False)
if set(map(Path,j['root_summary']))!=roots or len(j['targets'])!=j['file_count']!=8262:raise ValueError('exact cleanup roots/count')
if len({v['target']['path']for v in j['targets']})!=8262:raise ValueError('duplicate target')
allowed_authoritative=[R/'network/Solutions/RamanujanSourcePV.v1',D/'packed-million-clean-full-v1']
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def digest(p):
 h=hashlib.sha256()
 with p.open('rb')as f:
  for block in iter(lambda:f.read(1048576),b''):h.update(block)
 return h.hexdigest()
def record_ok(p,r):
 st=p.lstat()
 if p.is_symlink()or not stat.S_ISREG(st.st_mode)or st.st_uid!=os.getuid()or(st.st_size,st.st_dev,st.st_ino,st.st_mtime_ns,stat.S_IMODE(st.st_mode))!=(r['bytes'],r['device'],r['inode'],r['mtime_ns'],r['mode']):raise ValueError('file identity '+str(p))
 return st
def active_refs():
 ancestors={os.getpid()};current=os.getppid()
 while current>1:
  ancestors.add(current)
  try:current=int(Path('/proc') .joinpath(str(current),'stat').read_text().rsplit(')',1)[1].split()[1])
  except(FileNotFoundError,PermissionError):break
 refs=[];inaccessible=0
 for process in Path('/proc').iterdir():
  if not process.name.isdecimal()or int(process.name)in ancestors:continue
  try:
   if process.stat().st_uid!=os.getuid():continue
   cmd=(process/'cmdline').read_bytes().replace(b'\0',b' ').decode(errors='replace')
   if any(str(root)in cmd for root in roots):refs.append(dict(pid=int(process.name),kind='cmdline'))
   for fd in(process/'fd').iterdir():
    try:target=fd.readlink()
    except(FileNotFoundError,PermissionError):continue
    if any(str(target).startswith(str(root)+'/')for root in roots):refs.append(dict(pid=int(process.name),kind='open_fd'))
  except(FileNotFoundError,ProcessLookupError):continue
  except PermissionError:inaccessible+=1
 if refs:raise ValueError(('live owned process references',refs))
 return dict(checked_uid=os.getuid(),observed_references=refs,inaccessible_owned_processes=inaccessible)
first=active_refs();(out/'APPROVAL.json').write_text(json.dumps(dict(status='ROOT_APPROVED_EXACT_REGENERABLE_DUPLICATES_ONLY',authority='Owner standing reproducibility/cleanup instructions; Root review of exact preview and retained sources',preview_sha256=expected,time=now(),process_scan=first),indent=2)+'\n')
def verify(row):
 t=row['target'];a=row['retained_authoritative_copy'];p=Path(t['path']);q=Path(a['path']);root=Path(row['owned_completed_control_root'])
 if root not in roots or p.resolve()!=p or not p.is_relative_to(root)or p.suffix not in['.lean','.le']:raise ValueError('target ownership')
 if any(q.is_relative_to(x)for x in roots)or not any(q.is_relative_to(x)for x in allowed_authoritative)or q.resolve()!=q:raise ValueError('retained ownership')
 record_ok(p,t);record_ok(q,a)
 if t['sha256']!=a['sha256']or t['bytes']!=a['bytes']or digest(p)!=t['sha256']or digest(q)!=a['sha256']:raise ValueError('exact retained bytes')
 record_ok(p,t);record_ok(q,a)
 return t['bytes']
with ThreadPoolExecutor(max_workers=8)as pool:sizes=list(pool.map(verify,j['targets']))
if sum(sizes)!=j['bytes']:raise ValueError('total bytes')
second=active_refs();(out/'ALL_REVALIDATED.json').write_text(json.dumps(dict(status='ALL8262_TARGETS_AND_RETAINED_COPIES_REHASHED_BEFORE_DELETION',preview_sha256=expected,bytes=sum(sizes),time=now(),process_scan=second),indent=2)+'\n');print('ALL8262_REVALIDATED',flush=True)
removed=[]
try:
 for row in j['targets']:
  t=row['target'];a=row['retained_authoritative_copy'];p=Path(t['path']);q=Path(a['path']);record_ok(p,t);record_ok(q,a);p.unlink();removed.append(t['path'])
except BaseException as error:
 (out/'PARTIAL.json').write_text(json.dumps(dict(status='PARTIAL_CLEANUP_STOPPED',removed=removed,error=repr(error),time=now()),indent=2)+'\n');raise
if any(Path(v).exists()for v in removed):raise ValueError('target still present')
for row in j['targets']:record_ok(Path(row['retained_authoritative_copy']['path']),row['retained_authoritative_copy'])
result=dict(status='COMPLETE_ONLY_REVALIDATED_EXACT_DUPLICATE_TEMP_INPUTS_UNLINKED',time=now(),files=len(removed),logical_bytes=sum(sizes),allocated_bytes_before=j['allocated_bytes'],preview_sha256=expected,retained_authoritative_copies_present=True,accepted_proofs_code_meta_receipts_removed=False,active_study_inputs_removed=False,unmatched_eight_files_retained=True,consequence=j['cleanup_consequence'],regeneration=j['regeneration_tested'])
(out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
