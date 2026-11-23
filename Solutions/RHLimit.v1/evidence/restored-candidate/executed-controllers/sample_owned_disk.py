from pathlib import Path
import json,subprocess,time,hashlib
p=Path(__file__).resolve().parent;out=p/'owned-disk-observation';out.mkdir();target=p/'restored-default-replay';stop=p/'restored-default-launch/resources/RESULT.json';start=time.monotonic();maximum=0;samples=0
with(out/'samples.jsonl').open('w')as f:
 while True:
  actual=int(subprocess.check_output(['du','-s','-B1',str(target)],text=True).split()[0]);maximum=max(maximum,actual);samples+=1;row={'elapsed_seconds':time.monotonic()-start,'allocated_owned_bytes':actual};f.write(json.dumps(row)+'\n');f.flush()
  if stop.exists():break
  if time.monotonic()-start>14500:break
  time.sleep(30)
(out/'RESULT.json').write_text(json.dumps({'status':'COMPLETE_OWNED_ALLOCATED_DISK_SAMPLING','scope':str(target),'sample_count':samples,'sample_interval_seconds':30,'maximum_sampled_allocated_bytes':maximum,'final_sampled_allocated_bytes':actual,'elapsed_seconds':time.monotonic()-start,'controller_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'is_continuous_peak':False,'does_not_follow_union_symlinks':True},indent=2)+'\n')
