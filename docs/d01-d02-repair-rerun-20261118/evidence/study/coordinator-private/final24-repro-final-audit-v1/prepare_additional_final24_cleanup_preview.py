"""Inventory only three named duplicate roots and two completed plot installs."""
from pathlib import Path
import hashlib,json,os,stat,sys
sys.dont_write_bytecode=True
R=Path(__file__).resolve().parents[2]
F=R/'coordinator-private/twentyfour-normalized-frontiers-v1'
F20=R/'coordinator-private/twenty-normalized-frontiers-v1'
ROOTS=[Path('/data/ivy-final24-source-metadata-v2-v58fii9m'),Path('/data/ivy-final24-clean-analysis-xd3zs2rb'),Path('/data/ivy-final24-clean-analysis-q6e9a3qx'),F20/'plot-dependencies',F20/'plot-regeneration-dependencies']
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):
 h=hashlib.sha256()
 with p.open('rb')as s:
  for chunk in iter(lambda:s.read(1048576),b''):h.update(chunk)
 return h.hexdigest()
def pin(p):return{'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def actual_tree(root):
 need(root.resolve()==root and root.is_dir()and not root.is_symlink(),'exact unsymlinked owned root')
 mounts={Path(x.split()[4])for x in Path('/proc/self/mountinfo').read_text().splitlines()};need(not any(p==root or p.is_relative_to(root)for p in mounts),'no target mounts')
 files=[];directories=[]
 for p in sorted(root.rglob('*')):
  need(p.resolve()==p and not p.is_symlink(),'no symlink or path alias in owned tree')
  s=p.stat()
  if stat.S_ISDIR(s.st_mode):directories.append(str(p.relative_to(root)))
  else:
   need(stat.S_ISREG(s.st_mode),'only regular files and directories in target');files.append({'relative_path':str(p.relative_to(root)),'bytes':s.st_size,'allocated_bytes':s.st_blocks*512,'sha256':sha(p),'hardlink_count':s.st_nlink,'mode':stat.S_IMODE(s.st_mode)})
 return{'path':str(root),'files':files,'directories':directories,'regular_files':len(files),'logical_bytes':sum(x['bytes']for x in files),'allocated_file_bytes':sum(x['allocated_bytes']for x in files)}
def main():
 retained=R/'evidence/final24-additional-metadata-cleanup-retained-v1';manifest=retained/'RETAINED_ESSENTIAL_METADATA_EVIDENCE_MANIFEST.json';need(sha(manifest)=='2d6d25e4e5912f5629fc3a7c64a409e3f16b782851a34af2f1666c99f86c4885','exact retained essential manifest');m=json.loads(manifest.read_bytes());protected=[]
 for x in m['files']:
  p=Path(x['retained_path']);need(sha(p)==x['sha256']and p.stat().st_size==x['bytes'],'all retained essential bytes present');protected.append(pin(p))
 protected +=[pin(manifest),pin(retained/'PUBLIC_SELECTION_ADDRESS_ONLY_REFRESH_RECEIPT.json'),pin(retained/'historical-inputs/FRONTIER_ASSET_SELECTION_BEFORE_TEMP_RETENTION.json')]
 wheel_source=F20/'PLOT_WHEEL_SOURCE_RECEIPT.json';need(sha(wheel_source)=='20a3128dfd9c00e83641a13bcb63ece5cd371aba580facf05d0ae0f4d0e40596','exact wheel source receipt');w=json.loads(wheel_source.read_bytes());need(w['wheel_count']==len(w['wheels'])==11,'all11 pinned wheels');wheel_pins=[]
 for x in w['wheels']:
  p=F20/'plot-wheels'/x['wheel'];need(sha(p)==x['sha256']and p.stat().st_size==x['bytes'],'actual retained pinned wheel bytes');wheel_pins.append(pin(p))
 plot=F/'ACTUAL_PLOT_REGENERATION_RECEIPT.json';need(sha(plot)=='b12ba1e6d00ce4d6efe49098552dbc84320c8883c8f140fcdd33a1f348060f89','actual final two plot commands');p=json.loads(plot.read_bytes());need(len(p['commands'])==2 and all(x['exit_code']==0 and x['environment']['PYTHONDONTWRITEBYTECODE']=='1'for x in p['commands']),'both final commands finished without cache writes')
 clean=F/'ACTUAL_CLEAN_PORTABLE_ANALYSIS_REGENERATION.json';need(sha(clean)=='d6b6931e6bbafd5b961878185792f220370bed7a5c34038dc59c15811c553106','accepted successful seven-step control');need(json.loads(clean.read_bytes())['returncode']==0,'successful completed clean analysis')
 extra=[wheel_source,F20/'EXISTING_INSTALLED_ENVIRONMENT_PINS_V4.json',F20/'regenerate_plots.py',F20/'plot-requirements.lock',F20/'plot-requirements-with-hashes.lock',F20/'ACTUAL_PLOT_REGENERATION_RECEIPT.json',plot,F/'PLOT_EXECUTION_PLAN_FINAL24_UNSIGNED.json',F/'replay_existing_plot_environments_final24.py',clean,F/'ACTUAL_PORTABLE_SOURCE_NORMAL_O_OO_READ_DENIAL_CONTROLS.json',F/'FINITE_EXPLICIT_FUNCTIONS.json',R/'coordinator-private/portable-relocation-v2/portable-final24-source-review-v4.tar.gz',R/'evidence/final24-actual-resource-ledger-v1/FINAL24_ACTUAL_NUMERICAL_RESOURCE_LEDGER.json']
 trees=[actual_tree(root)for root in ROOTS]
 for tree in trees[3:]:
  mp=F20/(Path(tree['path']).name+'-INSTALLED_SOURCE_MANIFEST_V4.json');installed=json.loads(mp.read_bytes());expected={x['path']:(x['bytes'],x['sha256'])for x in installed['files']};actual={x['relative_path']:(x['bytes'],x['sha256'])for x in tree['files']};need(expected==actual and len(actual)==4263,'fresh complete installed manifest correspondence');extra.append(mp)
 protected +=[pin(x)for x in extra]+wheel_pins
 need(all(not any(Path(x['path']).is_relative_to(root)for root in ROOTS)for x in protected),'every irreplaceable/protected source remains outside target trees')
 out=R/'evidence/FINAL24_ADDITIONAL_METADATA_AND_PLOT_INSTALL_CLEANUP_PREVIEW_V1.json';need(not out.exists(),'fresh additional preview');value={'schema':'FINAL24_EXACT_ADDITIONAL_REGENERABLE_TREE_CLEANUP_PREVIEW_V1','status':'PREVIEW_ONLY_ESSENTIAL_EVIDENCE_RETAINED_NO_DELETION_OR_ROOT_APPLY_AUTHORITY','original27_target_preview_unchanged':{'path':str(R/'evidence/FINAL24_COMPLETED_REPRO_CHECKED_CLEANUP_EXACT_PREVIEW_V1.json'),'sha256':'a76127acdd9dc8f48cc6117215b09068549c58e0fae72aabf8a6905e5995b28f'},'targets':trees,'protected_retained_files':protected,'retained_essential_manifest':pin(manifest),'retained_wheels':wheel_pins,'completed_plot_receipt':pin(plot),'completed_clean_analysis_receipt':pin(clean),'target_count':5,'regular_file_count':sum(x['regular_files']for x in trees),'logical_bytes':sum(x['logical_bytes']for x in trees),'allocated_file_bytes':sum(x['allocated_file_bytes']for x in trees),'installed_plot_files_verified':8526,'pinned_wheels_retained':11,'regeneration_basis':['The three exact source-only /data copies are regenerable from retained source maps, clean-reproduction scripts and unchanged canonical/source-bundle bytes; every unique accepted or failed command receipt/log/map/denial helper was copied and hash checked first.','The two exact experiment-owned plot installs correspond to both immutable4263-file manifests and are regenerable from all11 retained SHA-pinned wheels; final two plot commands completed byte-identically. Source scripts/manifests/receipts/wheels and canonical outputs remain outside targets.'],'forbidden_targets':['Original canonical R mathematical sources, locked inputs, accepted proof artifacts, numerical source archives, receipts and wheels','Any other /data path, plot-cache or generic environment, other workspace, parent directory or unrelated host path'],'deletion_calls':0,'Root_authority_required_after_final_bundle_and_reproduction_acceptance':True};out.write_text(json.dumps(value,indent=2)+'\n');print(json.dumps({'preview':pin(out),'targets':5,'files':value['regular_file_count'],'logical_bytes':value['logical_bytes'],'allocated_bytes':value['allocated_file_bytes'],'installed_plot_files':8526,'retained_wheels':11}))
if __name__=='__main__':main()
