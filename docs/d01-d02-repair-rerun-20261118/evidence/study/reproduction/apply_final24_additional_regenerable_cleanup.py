"""Exact additional five-tree cleanup; read-only check unless Root authorizes apply."""
from pathlib import Path
import argparse,datetime,fcntl,hashlib,importlib.util,json,os,stat,subprocess,sys
sys.dont_write_bytecode=True
R=Path(__file__).resolve().parents[1]
BASE=R/'reproduction/apply_final24_regenerable_cleanup.py'
BASE_SHA='e959ab361ca4f7a93b05d0098b5142e95dd24f7770425f3c8ca1c6f94b9b3e7f'
PREVIEW_SHA='e9b64dd60c72247e11f53a3f1b9eb3b52239476d97c8d29582e1111d00643092'
F20=R/'coordinator-private/twenty-normalized-frontiers-v1'
TARGETS=sorted([str(Path('/data')/name)for name in ['ivy-final24-source-metadata-v2-v58fii9m','ivy-final24-clean-analysis-xd3zs2rb','ivy-final24-clean-analysis-q6e9a3qx']]+[str(F20/name)for name in ['plot-dependencies','plot-regeneration-dependencies']])
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb')as stream:
  for chunk in iter(lambda:stream.read(1048576),b''):h.update(chunk)
 return h.hexdigest()
def pin(p):return{'path':str(p),'sha256':sha(p)}
need(sha(BASE)==BASE_SHA,'unchanged original27-target reviewed helper')
spec=importlib.util.spec_from_file_location('reviewed_original_cleanup',BASE);base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
def unchanged(path,row):
 p=base.original(path);s=p.stat();need(stat.S_ISREG(s.st_mode)and s.st_size==row['bytes']and sha(p)==row['sha256']and s.st_nlink==row['hardlink_count']and stat.S_IMODE(s.st_mode)==row['mode'],'exact regular target bytes/mode/hardlinks unchanged');return s.st_blocks*512
def no_live_users():
 for proc in Path('/proc').glob('[0-9]*'):
  if int(proc.name)==os.getpid():continue
  try:
   cmd=(proc/'cmdline').read_bytes();maps=(proc/'maps').read_bytes()
  except(FileNotFoundError,ProcessLookupError,PermissionError):continue
  need(not any(t.encode()in cmd or t.encode()in maps for t in TARGETS),'live process command or mapped library names a target')
  links=[proc/'cwd']
  try:links+=list((proc/'fd').iterdir())
  except(FileNotFoundError,ProcessLookupError,PermissionError):continue
  for link in links:
   try:value=os.readlink(link)
   except(FileNotFoundError,ProcessLookupError,PermissionError,OSError):continue
   need(not any(value==t or value.startswith(t+'/')for t in TARGETS),'live process cwd or open file uses a target')
def main():
 parser=argparse.ArgumentParser(allow_abbrev=False);parser.add_argument('--preview',type=Path,required=True);parser.add_argument('--root-authorization',type=Path);parser.add_argument('--out',type=Path);mode=parser.add_mutually_exclusive_group(required=True);mode.add_argument('--check',action='store_true');mode.add_argument('--apply',action='store_true');a=parser.parse_args();need(a.preview.resolve().parent==R/'evidence'and sha(a.preview)==PREVIEW_SHA,'exact reviewed additional preview');v=base.load(a.preview);need(v['schema']=='FINAL24_EXACT_ADDITIONAL_REGENERABLE_TREE_CLEANUP_PREVIEW_V1'and v['target_count']==5 and v['deletion_calls']==0 and v['Root_authority_required_after_final_bundle_and_reproduction_acceptance']is True,'preview does not confer apply authority');need(sorted(x['path']for x in v['targets'])==TARGETS,'only exact three duplicate roots and two plot installs')
 for ref in v['protected_retained_files']:need(Path(ref['path']).is_file()and sha(ref['path'])==ref['sha256']and Path(ref['path']).stat().st_size==ref['bytes']and not any(Path(ref['path']).is_relative_to(Path(t))for t in TARGETS),'retained essential source/archive/receipt/wheel changed or is targeted')
 need(len(v['retained_wheels'])==11 and v['installed_plot_files_verified']==8526,'both completed installs and all11 retained regeneration wheels')
 files=[];directories=[];points=base.mounts()
 for tree in v['targets']:
  root=base.original(tree['path']);base.no_mount(root,points);need(root.is_dir(),'exact owned target directory');expected={x['relative_path']:x for x in tree['files']};actual={};ds=[]
  for path in root.rglob('*'):
   base.original(path)
   if path.is_dir():ds.append(path)
   else:need(path.is_file(),'only regular owned target entries');actual[str(path.relative_to(root))]=path
  need(set(actual)==set(expected)and{str(p.relative_to(root))for p in ds}==set(tree['directories']),'entire fresh tree file and directory census unchanged')
  for rel,path in sorted(actual.items()):unchanged(path,expected[rel]);files.append((path,expected[rel]))
  directories+=sorted(ds+[root],key=lambda p:len(p.parts),reverse=True)
 need(len(files)==v['regular_file_count']==29975,'exact complete additional regular-file count')
 ledger=base.load(R/'evidence/final24-actual-resource-ledger-v1/FINAL24_ACTUAL_NUMERICAL_RESOURCE_LEDGER.json');registry=R.parent/'EXPOSURE_LONGCHAIN_20261117_V1_RESOURCES'
 with(registry/'allocations.lock').open('a')as lock:
  fcntl.flock(lock,fcntl.LOCK_SH|fcntl.LOCK_NB);alloc=base.load(registry/'allocations.json')['allocations']
  for row in ledger['successful_cases']:
   ref=row['actual_resource_receipt'];need(sha(ref['path'])==ref['sha256'],'actual successful resource receipt unchanged');z=base.load(ref['path'])['reservation'];result=subprocess.run(['systemctl','--user','show',z['unit'],'--property=MainPID','--property=ActiveState'],capture_output=True,text=True);state=dict(s.split('=',1)for s in result.stdout.splitlines()if'='in s);need(state=={'MainPID':'0','ActiveState':'inactive'}and not(Path('/sys/fs/cgroup')/z['cgroup'].lstrip('/')).exists()and not any(x['run']==z['run']for x in alloc),'all24 scientific units/cgroups/leases must remain drained')
  no_live_users()
  if a.check:print(json.dumps({'status':'PASS_EXACT_ADDITIONAL_FIVE_TREE_PREVIEW_ALL_BYTES_AND_RETAINED_EVIDENCE_DRAIN_AND_NO_LIVE_USERS_NO_DELETION','targets':5,'regular_files':len(files),'payload_bytes':sum(x['bytes']for _,x in files),'deletion_calls':0}));return
  need(a.root_authorization is not None and a.out is not None,'explicit Root additional five-target authority required');auth=base.load(a.root_authorization);need(auth['schema']=='ROOT_EXACT_FINAL24_ADDITIONAL_REGENERABLE_CLEANUP_AUTHORITY_V1'and auth['status']=='ROOT_APPROVED_EXACT_FIVE_REGENERABLE_TREES_ONLY'and auth['reviewed_by']=='/root'and auth['preview']==pin(a.preview)and auth['helper_sha256']==sha(Path(__file__))and auth['approved_targets']==TARGETS,'exact reviewed Root source/preview/five-target authority');out=a.out.absolute();need(out.parent.resolve()==out.parent and out.is_relative_to(R/'evidence')and not out.exists(),'fresh durable output outside all targets');receipt={'status':'ADDITIONAL_CLEANUP_STARTED_AFTER_FULL_RETAINED_EVIDENCE_AND_PREDELETION_VERIFICATION','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'Root_authority':pin(a.root_authorization),'preview':pin(a.preview),'deleted_regular_files':[],'removed_empty_directories':[],'deleted_payload_bytes':0,'deleted_allocated_regular_bytes':0,'error':None,'original27_cleanup_executed_by_this_helper':False,'canonical_sources_archives_locked_inputs_proofs_certificates_receipts_wheels_or_unrelated_workspaces_deleted':False};pending=out.with_suffix(out.suffix+'.pending');need(not pending.exists(),'preserve earlier partial receipt')
  def save():
   with pending.open('w')as stream:stream.write(json.dumps(receipt,indent=2)+'\n');stream.flush();os.fsync(stream.fileno())
   os.replace(pending,out)
  save()
  try:
   for path,row in files:
    allocated=unchanged(path,row);path.unlink();receipt['deleted_regular_files'].append({'path':str(path),'sha256':row['sha256'],'bytes':row['bytes'],'allocated_bytes':allocated});receipt['deleted_payload_bytes']+=row['bytes'];receipt['deleted_allocated_regular_bytes']+=allocated
   for path in directories:base.no_mount(path,base.mounts());need(path.is_dir()and not any(path.iterdir()),'target directory changed or no longer empty');path.rmdir();receipt['removed_empty_directories'].append(str(path))
   receipt['status']='PASS_ONLY_EXACT_ROOT_APPROVED_FIVE_REGENERABLE_TREES_REMOVED_WITH_ALL_ESSENTIAL_EVIDENCE_RETAINED'
  except BaseException as error:receipt['status']='PARTIAL_ADDITIONAL_CLEANUP_STOPPED_ACTUAL_DELETIONS_RECORDED';receipt['error']=type(error).__name__+': '+str(error);raise
  finally:save()
  print(json.dumps({'status':receipt['status'],'receipt':pin(out),'regular_files_removed':len(receipt['deleted_regular_files']),'deleted_payload_bytes':receipt['deleted_payload_bytes'],'deleted_allocated_regular_bytes':receipt['deleted_allocated_regular_bytes']}))
if __name__=='__main__':main()
