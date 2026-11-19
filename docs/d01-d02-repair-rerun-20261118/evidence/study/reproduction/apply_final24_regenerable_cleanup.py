"""Apply only a Root-approved exact completed-experiment cleanup preview.
--check is read-only. --apply requires exact source, preview and target authority.
No original source, accepted archive, canonical receipt or certificate is a target.
"""
from pathlib import Path
import argparse,datetime,fcntl,hashlib,json,math,os,stat,subprocess,sys
sys.dont_write_bytecode=True
PREVIEW_SHA='a76127acdd9dc8f48cc6117215b09068549c58e0fae72aabf8a6905e5995b28f'
ARCHIVE_SHA='1da943a15aaebeb949a5ef472e82e97bb0d349d1914f2f0c01fbfe6f08a1de3a'
STUDY='ieantn-d01-d02-repair-rerun-20261118'
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def pin(p):return {'path':str(p),'sha256':sha(p)}
def load(p):
 def pairs(rows):
  d={}
  for k,v in rows:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 def finite(v):
  x=float(v);need(math.isfinite(x),'nonfinite JSON overflow');return x
 return json.loads(Path(p).read_bytes(),object_pairs_hook=pairs,parse_float=finite,parse_constant=lambda s:(_ for _ in()).throw(ValueError(s)))
def original(p):
 p=Path(p);need(p.is_absolute()and p.resolve()==p and not p.is_symlink(),'canonical unsymlinked target');return p
def mounts():return {Path(x.split()[4])for x in Path('/proc/self/mountinfo').read_text().splitlines()}
def no_mount(p,points):need(not p.is_mount()and not any(x==p or x.is_relative_to(p)for x in points),'cleanup target is or contains a mount')
def unchanged(p,row):
 p=original(p);s=p.stat();need(stat.S_ISREG(s.st_mode)and s.st_size==row['bytes']and sha(p)==row['sha256'],'regular target differs');need('hardlink_count'not in row or s.st_nlink==row['hardlink_count'],'target hardlink count changed');return s.st_blocks*512

def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--preview',type=Path,required=True);p.add_argument('--root-authorization',type=Path);p.add_argument('--out',type=Path);m=p.add_mutually_exclusive_group(required=True);m.add_argument('--check',action='store_true');m.add_argument('--apply',action='store_true');a=p.parse_args();need(sha(a.preview)==PREVIEW_SHA,'exact reviewed cleanup preview');v=load(a.preview);need(v['deletion_calls']==0 and v['requires_separate_Root_exact_target_approval_and_fresh_before_deletion_recheck']is True,'preview only, no assumed cleanup authority');r=a.preview.resolve().parents[1];need(r.name==STUDY,'canonical study receipt directory');ledgerpath=Path(v['source']['path']);need(sha(ledgerpath)==v['source']['sha256'],'exact completed24 resource ledger');ledger=load(ledgerpath);archive=r/'coordinator-private/portable-relocation-v2/portable-final24-source-review-v4.tar.gz';need(sha(archive)==ARCHIVE_SHA,'retained source regeneration archive');points=mounts();files=[];directories=[];targets=[]
 # Validate every regular file and every entire duplicate-tree census before
 # the first unlink/rmdir. Never broaden an accepted file list on the fly.
 for row in v['regenerable_unmanifested_cache_files']:
  f=original(row['path']);need(f.suffix=='.pyc'and f.parent.name=='__pycache__'and not f.is_relative_to(r),'only exact outside-source-cache leaf');unchanged(f,row);files.append((f,row));targets.append(str(f))
 for tree in v['owned_regenerable_metadata_duplicate_trees']:
  t=original(tree['path']);need(t.parent.name=='ivy-d01-d02-final24-clean-metadata-20261119-_lr2yqig'and t.name in ['source-tree','public-ledger-metadata-mirror-v1']and str(t).startswith('/data/'),'exact experiment-owned duplicate root');no_mount(t,points);expected={x['relative_path']:x for x in tree['files']};actual={};ds=[]
  for f in t.rglob('*'):
   original(f)
   if f.is_dir():ds.append(f)
   else:need(f.is_file(),'unexpected nonregular duplicate-tree entry');actual[str(f.relative_to(t))]=f
  need(set(actual)==set(expected),'duplicate-tree physical file census changed')
  for rel,f in actual.items():unchanged(f,expected[rel]);files.append((f,expected[rel]))
  directories+=sorted(ds+[t],key=lambda x:len(x.parts),reverse=True);targets.append(str(t))
 for row in v['empty_drained_namespace_directories']:
  t=original(row['path']);need(t.parts[-2:]==('isolation','root')and'/evidence/portable-relocated-reproduction-v2/FOLLOWUP-C'in str(t),'exact recorded namespace root');no_mount(t,points);need(t.is_dir()and not any(t.iterdir()),'namespace root no longer empty');directories.append(t);targets.append(str(t))
 need(len(targets)==27 and len(set(targets))==27,'exact24 empty roots,onecache,two metadata duplicates');need(all(not f.is_relative_to(r)for f,_ in files),'canonical study sources and accepted evidence protected');reg=r.parent/'EXPOSURE_LONGCHAIN_20261117_V1_RESOURCES'
 with(reg/'allocations.lock').open('a')as handle:
  fcntl.flock(handle,fcntl.LOCK_SH);alloc=load(reg/'allocations.json')['allocations']
  for row in ledger['successful_cases']:
   source=row['actual_resource_receipt'];need(sha(source['path'])==source['sha256'],'actual successful resource receipt changed');z=load(source['path'])['reservation'];q=subprocess.run(['systemctl','--user','show',z['unit'],'--property=MainPID','--property=ActiveState'],capture_output=True,text=True);state=dict(x.split('=',1)for x in q.stdout.splitlines()if'='in x);need(state=={'MainPID':'0','ActiveState':'inactive'}and not(Path('/sys/fs/cgroup')/z['cgroup'].lstrip('/')).exists()and not any(x['run']==z['run']for x in alloc),'scientific unit/cgroup/lease still active')
 # Exclude a still-running metadata user of the two owned duplicate trees.
 tree_targets=[str(Path(x['path']))for x in v['owned_regenerable_metadata_duplicate_trees']]
 for cmd in Path('/proc').glob('[0-9]*/cmdline'):
  if int(cmd.parent.name)==os.getpid():continue
  try:raw=cmd.read_bytes()
  except(FileNotFoundError,ProcessLookupError,PermissionError):continue
  need(not any(x.encode()in raw for x in tree_targets),'live process still names a metadata duplicate root')
 if a.check:print(json.dumps({'status':'PASS_EXACT_PREVIEW_TARGETS_SOURCES_REGENERATION_ARCHIVE_ALL24_DRAIN_AND_NO_LIVE_METADATA_USERS_NO_DELETION','regular_files':len(files),'targets':sorted(targets),'proposed_payload_bytes':sum(x['bytes']for _,x in files),'deletion_calls':0}));return
 need(a.root_authorization is not None and a.out is not None,'explicit Root authority and durable output required');auth=load(a.root_authorization);need(auth['schema']=='ROOT_EXACT_FINAL24_REGENERABLE_CLEANUP_AUTHORITY_V1'and auth['status']=='ROOT_APPROVED_EXACT_REGENERABLE_TARGETS_ONLY'and auth['reviewed_by']=='/root'and auth['preview']==pin(a.preview)and auth['helper_sha256']==sha(Path(__file__))and auth['approved_targets']==sorted(targets),'exact Root source/preview/target authority');out=a.out.absolute();need(out.parent.resolve()==out.parent and out.is_relative_to(r/'evidence')and not out.exists(),'fresh durable receipt outside all cleanup targets');receipt={'status':'CLEANUP_STARTED_AFTER_FULL_PREDELETION_VERIFICATION','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'Root_authorization':pin(a.root_authorization),'preview':pin(a.preview),'deleted_regular_files':[],'removed_empty_directories':[],'deleted_payload_bytes':0,'deleted_allocated_regular_bytes':0,'error':None,'canonical_sources_archives_locked_inputs_proofs_certificates_receipts_and_other_workspaces_deleted':False};tmp=out.with_suffix(out.suffix+'.pending');need(not tmp.exists(),'preserve prior cleanup partial receipt')
 def save():tmp.write_text(json.dumps(receipt,indent=2)+'\n');os.replace(tmp,out)
 save()
 try:
  for f,row in files:
   allocated=unchanged(f,row);f.unlink();receipt['deleted_regular_files'].append({'path':str(f),'sha256':row['sha256'],'bytes':row['bytes'],'allocated_bytes':allocated});receipt['deleted_payload_bytes']+=row['bytes'];receipt['deleted_allocated_regular_bytes']+=allocated
  for t in directories:no_mount(t,mounts());need(t.is_dir()and not any(t.iterdir()),'directory no longer empty');t.rmdir();receipt['removed_empty_directories'].append(str(t))
  receipt['status']='PASS_ONLY_EXACT_APPROVED_REGENERABLE_TARGETS_REMOVED_AFTER_REPRODUCTION_CHECKS'
 except BaseException as e:receipt['status']='PARTIAL_CLEANUP_STOPPED_PRESERVED_ACTUAL_DELETIONS';receipt['error']=type(e).__name__+': '+str(e);raise
 finally:save()
 print(json.dumps({'status':receipt['status'],'receipt':pin(out),'deleted_payload_bytes':receipt['deleted_payload_bytes'],'deleted_allocated_regular_bytes':receipt['deleted_allocated_regular_bytes'],'regular_files_removed':len(receipt['deleted_regular_files']),'empty_directories_removed':len(receipt['removed_empty_directories'])}))
if __name__=='__main__':main()
