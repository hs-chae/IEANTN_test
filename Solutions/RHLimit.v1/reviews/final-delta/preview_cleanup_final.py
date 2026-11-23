#!/usr/bin/env python3
"""PREVIEW ONLY. No unlink/rmtree or host/cache changes are implemented."""
from pathlib import Path,PurePosixPath
import argparse,collections,datetime,hashlib,json,math,os,stat,tarfile
D=Path('/data/ivy-rh-limit-20261122');P=D/'publication';N=Path('/ryu/hyunsik/playground/independence/codex/ivy/ieantn-rh-continuation-20261122/network')
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);a=p.parse_args();out=a.out.resolve()
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(f):
 need(f.is_file()and not f.is_symlink(),'regular input:'+str(f));h=hashlib.sha256()
 with f.open('rb')as s:
  for b in iter(lambda:s.read(1048576),b''):h.update(b)
 return h.hexdigest()
def read(f):
 def pairs(items):
  d={}
  for k,v in items:need(k not in d,'duplicate key');d[k]=v
  return d
 def fl(raw):
  v=float(raw);need(math.isfinite(v),'nonfinite');return v
 return json.loads(f.read_bytes(),object_pairs_hook=pairs,parse_float=fl,parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfinite')))
def info(f):
 s=f.lstat();return {'path':str(f),'logical_bytes':s.st_size,'allocated_bytes':s.st_blocks*512,'device':s.st_dev,'inode':s.st_ino,'hardlinks':s.st_nlink,'is_symlink':stat.S_ISLNK(s.st_mode),'is_regular':stat.S_ISREG(s.st_mode)}
def tree_info(root):
 files=[info(x)for x in root.rglob('*')if x.is_file()or x.is_symlink()];return {'path':str(root),'file_entries':len(files),'logical_bytes_sum':sum(x['logical_bytes']for x in files),'allocated_bytes_sum_counting_hardlink_entries':sum(x['allocated_bytes']for x in files),'symlink_entries':sum(x['is_symlink']for x in files),'unique_file_inodes':len({(x['device'],x['inode'])for x in files})}
need(not out.exists(),'fresh preview output')
main=read(P/'restored-default-replay/RESULT.json');need(main['status']=='PASS_ALL_RH_LIMIT_FRESH_SOURCE_NUMERICAL_AND_CANONICAL_ROUTES','accepted full replay')
index=collections.defaultdict(list);banks=[]
for label in ['pi','spectral','octic','canonical']:
 root=P/'restored-default-replay'/label;r=read(root/'RESULT.json');step=[x for x in main['steps']if x['component']==label];need(len(step)==1 and step[0]['accepted']is True and sha(root/'RESULT.json')==step[0]['receipt_sha256'],'retained bank acceptance');b=read(root/'BUILD.json');need(b['status']=='PASS','retained build pass')
 for row in b['modules']:
  f=root/'objects'/(row['module'].replace('.','/')+'.olean');need(type(row['returncode'])is int and row['returncode']==0 and sha(f)==row['object_sha256'],'retained accepted object');index[row['object_sha256']].append(str(f))
 banks.append({'path':str(root/'objects'),'RESULT_sha256':sha(root/'RESULT.json'),'BUILD_sha256':sha(root/'BUILD.json'),'verified_objects':len(b['modules'])})
# The accepted111+3 analytic bank offers additional exact copies, only if its
# object hashes were actually preserved in the complete accepted BUILD receipt.
root=P/'restored-default-replay/analytic-absolute/base';b=read(root/'BUILD.json')
if b['status']=='PASS'and all('object_sha256'in row for row in b['modules']):
 for row in b['modules']:
  f=root/'objects'/(row['module'].replace('.','/')+'.olean');need(type(row['returncode'])is int and row['returncode']==0 and sha(f)==row['object_sha256'],'retained analytic object');index[row['object_sha256']].append(str(f))
 banks.append({'path':str(root/'objects'),'parent_RESULT_sha256':sha(root.parent/'RESULT.json'),'BUILD_sha256':sha(root/'BUILD.json'),'verified_objects':len(b['modules'])})
eligible=[];preserve=[];roots=[]
for name in ['baseline-objects','baseline-pnt-objects','work-objects','work-pnt-objects']:
 root=D/'pi'/name;need(root.is_dir()and not root.is_symlink(),'exact owned preview root');roots.append(tree_info(root))
 for f in sorted(root.rglob('*')):
  if f.is_dir()and not f.is_symlink():continue
  x=info(f)
  if x['is_regular']and not x['is_symlink']and f.suffix=='.olean':
   x['sha256']=sha(f)
   if x['sha256']in index:
    keep=Path(index[x['sha256']][0]);need(sha(keep)==x['sha256'],'retained byte copy');k=info(keep);x.update({'retained_accepted_copy':str(keep),'retained_copy_sha256':x['sha256'],'same_inode_as_retained':(x['device'],x['inode'])==(k['device'],k['inode'])});eligible.append(x);continue
  x['reason']='Not a regular .olean with an identical, separately retained accepted proof-bank copy.';preserve.append(x)
archive=P/'RH_LIMIT_SOURCE_CANDIDATE.tar.gz';need(sha(archive)=='7035c795dd16cba6f9e249f03541d44a91a1fdb724f03498efb86ec8bb5733f2','retained candidate archive');stage=P/'candidate-source';restored=P/'restored-candidate';need(stage.is_dir()and not stage.is_symlink()and restored.is_dir()and not restored.is_symlink(),'owned stage and retained restore')
archive_rows=[];seen=set()
with tarfile.open(archive,'r:gz')as tf:
 for m in tf:
  if m.isdir():continue
  q=PurePosixPath(m.name);need(m.isfile()and not q.is_absolute()and'..'not in q.parts and m.name not in seen,'safe unique regular archive member');seen.add(m.name);f=tf.extractfile(m);need(f is not None,'archive stream');h=hashlib.sha256()
  for block in iter(lambda:f.read(1048576),b''):h.update(block)
  digest=h.hexdigest();need(sha(stage/m.name)==digest==sha(restored/m.name),'archive/stage/retained restore exact member:'+m.name);archive_rows.append({'path':m.name,'bytes':m.size,'sha256':digest})
actual={str(f.relative_to(stage))for f in stage.rglob('*')if f.is_file()or f.is_symlink()};need(actual==seen,'exact archive/stage membership');need(not any(Path(r['path']).suffix=='.olean'for r in archive_rows),'source stage contains no accepted proof objects')
figure=D/'reviews/resource-figure';ex=figure/'export-v1';ready=read(figure/'EXPORT_READY.json');need(ready['files_including_manifest']==19 and sha(ex/'MANIFEST.json')==ready['manifest_sha256'],'accepted figure export');fm=read(ex/'MANIFEST.json');need(len(fm['files'])==18 and{str(f.relative_to(ex))for f in ex.rglob('*')if f.is_file()}=={x['path']for x in fm['files']}|{'MANIFEST.json'},'exact19figure export')
for row in fm['files']:need(sha(ex/row['path'])==row['sha256']==sha(N/'Solutions/RHLimit.v1/reports/resources'/row['path']),'retained figure artifact copy')
dep=read(ex/'DEPENDENCIES.json');need(dep['status']=='PASS_PLOTTING_ONLY_HASH_LOCKED_DEPENDENCIES'and dep['hash_locked_install_returncode']==0 and dep['pins_verified_equal_to_installed_versions']is True,'actual hashlocked reinstall accepted')
for rel,h in dep['files'].items():need(sha(figure/rel)==h==sha(ex/rel),'retained dependency evidence')
first=read(ex/'RENDER_FIRST.json');repeat=read(ex/'RENDER_REPEAT.json');det=read(ex/'DETERMINISM.json');need(det['status']=='PASS_TWO_ACTUAL_BYTE_IDENTICAL_FINAL_RENDERS'and sha(ex/'RENDER_FIRST.json')==det['render_first_receipt_sha256']and sha(ex/'RENDER_REPEAT.json')==det['render_repeat_receipt_sha256'],'actual two render receipts')
for ext in ['svg','png']:
 name='resource-replay.'+ext;need(first['output_sha256'][name]==repeat['output_sha256'][name]==sha(ex/name)==sha(figure/'final-v1'/name)==sha(figure/'final-repeat-v1'/name),'two actual identical rendered outputs')
plot=[];absent=[]
for name in ['venv','uv-cache','wheelhouse','pipcache','pip-cache']:
 f=figure/name
 if f.exists():need(f.is_dir()and not f.is_symlink(),'owned plotting temporary root');plot.append(tree_info(f))
 else:absent.append(str(f))
result={'status':'VERIFIED_PREVIEW_ONLY_NOT_DELETED','deletion_authorized':False,'checker_sha256':sha(Path(__file__)),'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'retained_accepted_banks':banks,'exact_owned_object_roots':roots,'eligible_regular_olean_copies':eligible,'preserve_unmatched_or_other_entries':preserve,'source_stage':{'target':str(stage),'retained_archive':str(archive),'archive_sha256':sha(archive),'retained_restored_source':str(restored),'archive_member_count':len(archive_rows),'archive_members':archive_rows,'tree':tree_info(stage),'member_by_member_match':True},'plotting_temporaries':plot,'plotting_absent_requested_cache_names':absent,'plot_preserve':['generate_resource_figure.py','seal_export.py','README.md','EXPORT_READY.json','DEPENDENCIES.json','requirements.freeze.txt','requirements.lock.txt','hash-locked-environment.stdout','hash-locked-environment.stderr','export-v1','final-v1','final-repeat-v1','history','preview-v1','preview-v2','preview-v3','matplotlib-config'],'plot_conditions_verified':{'compact_export_files':19,'manifest_sha256':sha(ex/'MANIFEST.json'),'actual_hashlocked_reinstall_returncode':0,'two_actual_identical_renders':True,'public_source_export_matches':True,'uv_cache_is_owned_equivalent_of_package_download_cache':True},'metrics_boundary':'Logical byte sums and allocated block sums describe the selected directory entries. Hardlinks/shared extents can double count; shared host free-filesystem changes are not equivalent to bytes removed. No deletion or claimed freed-space result is made.','preservation_boundary':'All accepted proof banks, sources, logs, original candidate archive, restored candidate, generic/shared caches, host processes and unrelated workspaces remain untouched. Only Root can approve this exact target preview before a separate deletion step.'}
out.parent.mkdir(parents=True,exist_ok=True);tmp=out.with_suffix(out.suffix+'.tmp');tmp.write_text(json.dumps(result,indent=2,allow_nan=False)+'\n');os.replace(tmp,out);print(json.dumps({'status':result['status'],'eligible_olean_copies':len(eligible),'unmatched_preserved':len(preserve),'eligible_logical_bytes':sum(x['logical_bytes']for x in eligible),'eligible_allocated_entry_bytes':sum(x['allocated_bytes']for x in eligible),'stage_members':len(archive_rows),'plot_targets':plot,'receipt_sha256':sha(out)}))
