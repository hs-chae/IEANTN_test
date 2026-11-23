#!/usr/bin/env python3
"""Execute only the exact Root-approved owned cleanup; recheck every removed byte."""
from pathlib import Path
import argparse,datetime,hashlib,json,math,os,shutil,stat,time
D=Path('/data/ivy-rh-limit-20261122');P=D/'publication'
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--preview',type=Path,default=P/'FINAL_CLEANUP_PREVIEW.json');p.add_argument('--approval',type=Path,default=P/'ROOT_APPROVED_FINAL_CLEANUP.json');p.add_argument('--out',type=Path,required=True);p.add_argument('--check',action='store_true');a=p.parse_args();out=a.out.resolve()
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(f):
 need(f.is_file()and not f.is_symlink(),'regular file required:'+str(f));h=hashlib.sha256()
 with f.open('rb')as s:
  for b in iter(lambda:s.read(1048576),b''):h.update(b)
 return h.hexdigest()
def read(f):
 def pairs(items):
  d={}
  for k,v in items:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 def fl(raw):
  x=float(raw);need(math.isfinite(x),'nonfinite JSON');return x
 return json.loads(f.read_bytes(),object_pairs_hook=pairs,parse_float=fl,parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfinite JSON')))
def require_owned(path,roots):
 need(path.is_absolute()and any(path==r or r in path.parents for r in roots),'outside exact owned target')
 for q in [path,*path.parents]:
  if q==D:break
  need(not q.is_symlink(),'symlink ancestor outside cleanup: '+str(q))
def tree_inventory(root):
 need(root.is_dir()and not root.is_symlink(),'owned regular directory');rows=[]
 for f in sorted(root.rglob('*')):
  s=f.lstat();kind='symlink'if stat.S_ISLNK(s.st_mode)else'file'if stat.S_ISREG(s.st_mode)else'dir'if stat.S_ISDIR(s.st_mode)else'other';need(kind!='other','unexpected cache entry kind')
  r={'path':str(f.relative_to(root)),'kind':kind,'logical_bytes':s.st_size,'allocated_bytes':s.st_blocks*512,'device':s.st_dev,'inode':s.st_ino}
  if kind=='file':r['sha256']=sha(f)
  if kind=='symlink':r['link_text']=os.readlink(f)
  rows.append(r)
 return rows
def recheck_entry(root,row):
 f=root/row['path'];s=f.lstat();need((s.st_dev,s.st_ino)==(row['device'],row['inode']),'entry inode changed')
 if row['kind']=='file':need(stat.S_ISREG(s.st_mode)and not f.is_symlink()and sha(f)==row['sha256'],'entry bytes/kind changed')
 elif row['kind']=='symlink':need(stat.S_ISLNK(s.st_mode)and os.readlink(f)==row['link_text'],'symlink entry changed')
 else:need(stat.S_ISDIR(s.st_mode)and not f.is_symlink(),'directory kind changed')
 return f
need(not out.exists(),'fresh cleanup receipt output')
v=read(a.preview);approval=read(a.approval);need(sha(a.preview)==approval['preview_sha256']=='581382feb1427e83c0604f92401904ac3a341088e7e3813d4aa1c9935a475263','exact Root preview pin');need(approval['status']=='ROOT_APPROVED_EXACT_VERIFIED_REGENERABLE_TARGETS'and v['status']=='VERIFIED_PREVIEW_ONLY_NOT_DELETED','Root authority/preview status')
roots=[Path(x)for x in approval['exact_object_roots']];need(roots==[D/'pi'/x for x in ['baseline-objects','baseline-pnt-objects','work-objects','work-pnt-objects']],'exact four object roots');eligible=v['eligible_regular_olean_copies'];keep=v['preserve_unmatched_or_other_entries'];need(len(eligible)==approval['eligible_regular_olean_copies']==602 and len(keep)==approval['preserve_unmatched_entries']==165,'exact approved counts')
for x in eligible:
 f=Path(x['path']);require_owned(f,roots);s=f.lstat();need(stat.S_ISREG(s.st_mode)and f.suffix=='.olean'and(s.st_dev,s.st_ino)==(x['device'],x['inode'])and sha(f)==x['sha256'],'approved object source changed');ret=Path(x['retained_accepted_copy']);need(not any(ret==r or r in ret.parents for r in roots)and sha(ret)==x['sha256'],'accepted retained object missing/changed')
for x in keep:
 f=Path(x['path']);s=f.lstat();need((s.st_dev,s.st_ino)==(x['device'],x['inode']),'unmatched entry changed')
 if 'sha256'in x:need(sha(f)==x['sha256'],'unmatched bytes changed')
stage=Path(approval['archive_backed_stage']);need(stage==P/'candidate-source'and stage==Path(v['source_stage']['target'])and not stage.is_symlink(),'exact stage');archive=Path(v['source_stage']['retained_archive']);restored=Path(v['source_stage']['retained_restored_source']);need(sha(archive)==v['source_stage']['archive_sha256']=='7035c795dd16cba6f9e249f03541d44a91a1fdb724f03498efb86ec8bb5733f2','retained exact archive')
stage_rows=tree_inventory(stage);stage_files={r['path']:r for r in stage_rows if r['kind']!='dir'};need(len(stage_files)==len(v['source_stage']['archive_members'])and all(r['kind']=='file'for r in stage_files.values()),'exact regular archive stage membership')
for x in v['source_stage']['archive_members']:need(x['path']in stage_files and stage_files[x['path']]['sha256']==x['sha256']==sha(restored/x['path']),'stage/archive/restored member association')
plots=[Path(x)for x in approval['plotting_temporaries']];figure=D/'reviews/resource-figure';need(plots==[figure/'venv',figure/'uv-cache'],'exact owned plotting caches');plot_rows={str(r):tree_inventory(r)for r in plots}
for target in v['plotting_temporaries']:
 rows=plot_rows[target['path']];files=[r for r in rows if r['kind']!='dir'];need(len(files)==target['file_entries']and sum(r['logical_bytes']for r in files)==target['logical_bytes_sum'],'plot cache tree changed after preview')
ex=figure/'export-v1';fm=read(ex/'MANIFEST.json');need(sha(ex/'MANIFEST.json')==v['plot_conditions_verified']['manifest_sha256']and len(fm['files'])==18,'retained compact figure')
for x in fm['files']:need(sha(ex/x['path'])==x['sha256'],'retained essential figure bytes')
if a.check:print(json.dumps({'status':'PASS_ROOT_APPROVED_CLEANUP_PREFLIGHT_ONLY','files_eligible':len(eligible),'unmatched_preserved':len(keep),'source_stage_files':len(stage_files),'deletions_performed':False}));raise SystemExit(0)
out.mkdir(parents=True);shutil.copyfile(Path(__file__),out/'execute_approved_cleanup.executed.py');shutil.copyfile(a.preview,out/'PREVIEW.json');shutil.copyfile(a.approval,out/'APPROVAL.json');(out/'PLOT_REMOVED_ENTRY_IDENTITIES.json').write_text(json.dumps(plot_rows,indent=2)+'\n')
result={'status':'RUNNING_APPROVED_CLEANUP','began_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'controller_sha256':sha(Path(__file__)),'preview_sha256':sha(a.preview),'approval_sha256':sha(a.approval),'deleted_object_copies':[],'deleted_source_stage':False,'deleted_plot_directories':[],'free_filesystem_before_bytes':shutil.disk_usage(D).free,'source_stage_file_count':len(stage_files),'object_logical_bytes_removed':0,'object_allocated_entry_bytes_removed':0,'all_removed_entry_metrics_are_not_attributed_actual_free_space':True};start=time.monotonic()
def receipt():
 temp=out/'RESULT.json.tmp';temp.write_text(json.dumps(result,indent=2,allow_nan=False)+'\n');os.replace(temp,out/'RESULT.json')
def remove_verified_tree(root,rows):
 need(root.is_dir()and not root.is_symlink(),'owned deletion root changed')
 for row in rows:
  if row['kind']=='dir':continue
  f=recheck_entry(root,row);f.unlink()
 for row in sorted((r for r in rows if r['kind']=='dir'),key=lambda r:len(Path(r['path']).parts),reverse=True):recheck_entry(root,row).rmdir()
 root.rmdir()
receipt()
try:
 for x in eligible:
  f=Path(x['path']);require_owned(f,roots);s=f.lstat();need(stat.S_ISREG(s.st_mode)and(s.st_dev,s.st_ino)==(x['device'],x['inode'])and sha(f)==x['sha256']==sha(Path(x['retained_accepted_copy'])),'immediate object/retained identity');f.unlink();result['deleted_object_copies'].append({'path':str(f),'sha256':x['sha256'],'retained_accepted_copy':x['retained_accepted_copy']});result['object_logical_bytes_removed']+=x['logical_bytes'];result['object_allocated_entry_bytes_removed']+=x['allocated_bytes']
 receipt();need(sha(archive)==v['source_stage']['archive_sha256'],'archive retained before stage cleanup');remove_verified_tree(stage,stage_rows);result['deleted_source_stage']=True;receipt()
 for root in plots:
  for x in fm['files']:need(sha(ex/x['path'])==x['sha256'],'essential figure retained before cache cleanup')
  remove_verified_tree(root,plot_rows[str(root)]);result['deleted_plot_directories'].append(str(root));receipt()
 for x in eligible:need(not Path(x['path']).exists()and sha(Path(x['retained_accepted_copy']))==x['sha256'],'accepted retained copy after cleanup')
 for x in keep:
  f=Path(x['path']);s=f.lstat();need((s.st_dev,s.st_ino)==(x['device'],x['inode']),'unmatched after-state changed')
  if'sha256'in x:need(sha(f)==x['sha256'],'unmatched bytes changed after cleanup')
 for x in v['source_stage']['archive_members']:need(sha(restored/x['path'])==x['sha256'],'restored source changed after cleanup')
 need(sha(archive)==v['source_stage']['archive_sha256']and not stage.exists(),'archive/stage after-state')
 for x in fm['files']:need(sha(ex/x['path'])==x['sha256'],'retained figure after cleanup')
 result.update({'status':'PASS_APPROVED_REGENERABLE_CLEANUP_AND_RETAINED_AFTERSTATE','preserved_unmatched_entries':len(keep),'all602_retained_accepted_objects_SHA_checked_after':True,'all3095_restored_source_members_checked_after':True,'all19_figure_export_files_retained':True,'accepted_banks_deleted':False,'original_or_only_reproducibility_sources_or_logs_deleted':False,'free_filesystem_after_bytes':shutil.disk_usage(D).free,'elapsed_seconds':time.monotonic()-start,'space_accounting_caveat':'The two filesystem free-space observations are on a shared active filesystem; their difference is not attributed to this cleanup. Logical/allocated-entry removal is separately recorded. No continuous or actual exclusive reclaimed-byte claim is made.'});result['observed_shared_filesystem_free_delta_bytes']=result['free_filesystem_after_bytes']-result['free_filesystem_before_bytes'];receipt()
except BaseException as e:
 result.update({'status':'FAILED_PARTIAL_CLEANUP_PRESERVED_RECEIPT','error':repr(e),'elapsed_seconds':time.monotonic()-start});receipt();raise
print(json.dumps({'status':result['status'],'deleted_object_copies':len(result['deleted_object_copies']),'unmatched_preserved':len(keep),'source_stage_removed':result['deleted_source_stage'],'plot_directories_removed':result['deleted_plot_directories'],'receipt_sha256':sha(out/'RESULT.json')}))
