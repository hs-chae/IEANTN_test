#!/usr/bin/env python3
"""Collect already executed run evidence without changing historical receipts."""
import argparse,hashlib,json,re,shutil
from pathlib import Path

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def owned_bytes(root):return sum(p.stat().st_blocks*512 for p in root.rglob('*') if p.is_file() and not p.is_symlink())
def cpu(logs):
 total_user=total_system=0.;records=0;peak=0
 for p in logs:
  t=p.read_text(errors='replace');u=re.search(r'User time \(seconds\): ([0-9.]+)',t);s=re.search(r'System time \(seconds\): ([0-9.]+)',t);m=re.search(r'Maximum resident set size \(kbytes\): (\d+)',t)
  if u and s:total_user+=float(u[1]);total_system+=float(s[1]);records+=1
  if m:peak=max(peak,int(m[1]))
 return dict(recorded_user_CPU_seconds=round(total_user,3),recorded_system_CPU_seconds=round(total_system,3),GNU_time_records=records,max_recorded_individual_compiler_RSS_KiB=peak)
def main():
 p=argparse.ArgumentParser(description=__doc__,allow_abbrev=False);p.add_argument('--study',type=Path,required=True);p.add_argument('--data',type=Path,required=True);a=p.parse_args();S=a.study.resolve(strict=True);D=a.data.resolve(strict=True);out=S/'evidence/reproduction'
 out.mkdir(parents=True,exist_ok=True);summary=[];copies=[]
 def copy(source,dest):
  target=out/dest;target.parent.mkdir(parents=True,exist_ok=True)
  if target.exists() and target.read_bytes()!=source.read_bytes():raise ValueError('Refuse to overwrite different historical evidence '+str(target))
  if not target.exists():shutil.copyfile(source,target)
  if sha(target)!=sha(source):raise ValueError('Evidence copy mismatch')
  copies.append({'path':str(target.relative_to(S)),'sha256':sha(target),'bytes':target.stat().st_size})
 for label,run,compile_run,kind in [
  ('unchanged244',D/'fresh-octic244-v2',D/'fresh-octic244-v2','Fresh unchanged application baseline; generic libraries reused.'),
  ('historical297',D/'fresh-final-all-v1',D/'fresh-final-all-v1','Exact historical earlier source; one later comment correction has separate replay.'),
  ('relocated300',D/'relocated-reproduction-v2/run',D/'relocated-reproduction-v2/run/compile','Clean relocated300source pipeline; actual24headline+helper audit and6controls.'),
  ('gaussian53',D/'gaussian-gap/relocated-v1/run',D/'gaussian-gap/relocated-v1/run/compile','Clean relocated53source Gaussian/Fourier/ANT pipeline; actual6canonicalheadline,11roots/12edges and6controls.')]:
  execution=compile_run/'EXECUTION.json';e=json.loads(execution.read_text());full=json.loads((run/'RESULT.json').read_text()) if (run/'RESULT.json').exists() else e
  logs=list(compile_run.glob('logs/*.stderr'))+list((run/'audit').glob('logs/*.stderr'))
  row=dict(label=label,scope=kind,source_first_PV=False,status=full['status'],compiled_application_modules=e['compiled_modules'],compile_wall_seconds=e['seconds'],full_pipeline_wall_seconds=full['seconds'],compiler_phase_sampled_peak_tree_RSS_bytes=e['sampled_peak_owned_tree_RSS_bytes'],compiler_phase_largest_child_RSS_KiB=e['peak_individual_child_RSS_KiB'],compiler_phase_final_allocated_disk_bytes=e['owned_allocated_disk_bytes'],current_final_owned_run_tree_bytes=owned_bytes(run),observed_compiler_SIGKILL_events=e['observed_SIGKILL_compiler_events'],resource_limit='64GiB per compiler; currentcapacity-based hostreserve;4workers for300,2for53',limitations='Aggregate RAM is sampled, exact individual GNU peaks retained; disk is final allocation, not a claimed exact peak. No observed own compiler SIGKILL is not a host-wide OOM audit.',**cpu(logs))
  summary.append(row)
  for source in [run/'RESULT.json',run/'LAUNCH.json',compile_run/'EXECUTION.json',compile_run/'PLAN.json',compile_run/'TREE_RSS.csv',run/'audit/RESULT.json',run/'audit/ACCEPTANCE.json']:
   if source.exists():copy(source,Path(label)/source.relative_to(run))
  for source in compile_run.glob('logs/*.stdout'):copy(source,Path(label)/'compiler-stdout'/source.name)
  for source in compile_run.glob('logs/*.stderr'):copy(source,Path(label)/'compiler-stderr'/source.name)
  for source in (run/'audit').glob('logs/*'):
   if source.is_file():copy(source,Path(label)/'audit-logs'/source.name)
 # Historical execution before the single comment correction remains independently recoverable.
 copy(D/'fresh-final-all-v1/source/Lee2023LiteralRow.lean',Path('historical297/source-delta/Lee2023LiteralRow.before-comment.lean'))
 (out/'RUN_SUMMARY.json').write_text(json.dumps({'status':'DESCRIPTIVE_EVIDENCE_COPY_NOT_NEW_MATHEMATICAL_ACCEPTANCE','runs':summary},indent=2)+'\n')
 (out/'COPIED_FILES.json').write_text(json.dumps({'files':copies},indent=2)+'\n')
 print(json.dumps({'copied_files':len(copies),'bytes':sum(x['bytes'] for x in copies),'rows':[{k:q[k] for k in ['label','compiled_application_modules','full_pipeline_wall_seconds','recorded_user_CPU_seconds','recorded_system_CPU_seconds']} for q in summary]}))
if __name__=='__main__':main()
