#!/usr/bin/env python3
"""Independent pre-child /proc sampler; observations are not proof acceptance."""
from pathlib import Path
import argparse,datetime,hashlib,json,os,re,subprocess,time
from monitor_demand_resources import disk,identity,need
S=Path(__file__).resolve().parents[1]
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--pid',type=int,required=True);p.add_argument('--path',type=Path,action='append',required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--ready-file',type=Path,required=True);p.add_argument('--stop-file',type=Path,required=True);p.add_argument('--interval',type=float,default=1.0);a=p.parse_args();c=json.loads((S/'BUILD_CONTEXT.json').read_text());owned=Path(c['new_application_object_root']).resolve().parent;out=a.out.resolve();ready=a.ready_file.resolve();stop=a.stop_file.resolve();paths=[q.resolve()for q in a.path]
 need(.1<=a.interval<=10 and out.is_relative_to(owned)and not out.exists()and ready.is_relative_to(owned)and not ready.exists()and stop.is_relative_to(owned)and not stop.exists(),'fresh owned observer paths/interval');need(all(q.is_relative_to(owned)for q in paths),'owned measured paths');token=identity(a.pid);need(token is not None,'actual fixed live launcher');out.mkdir(parents=True);started=time.monotonic();ticks=os.sysconf('SC_CLK_TCK');seen_cpu={};peaks=dict(rss_bytes=0,pss_bytes=0,virtual_bytes=0);maxdisk=dict(logical_bytes=0,allocated_bytes=0,files=0);latest_disk={};last_disk=-20;count=0;reason='PARENT_EXIT'
 with(out/'samples.jsonl').open('x')as stream:
  while identity(a.pid)==token:
   links=[tuple(map(int,line.split()))for line in subprocess.check_output(['ps','-eo','pid=,ppid='],text=True).splitlines()];tree={a.pid}
   while True:
    expanded=tree|{pid for pid,parent in links if parent in tree}
    if expanded==tree:break
    tree=expanded
   details=[];rss=pss=virtual=0
   for pid in sorted(tree):
    try:
     base=Path('/proc')/str(pid);pid_token=identity(pid);status=(base/'status').read_text();stat=(base/'stat').read_text();fields=stat[stat.rfind(')')+2:].split();user=int(fields[11])/ticks;system=int(fields[12])/ticks;key=str(pid)+':'+str(pid_token);old=seen_cpu.get(key,(0.,0.));seen_cpu[key]=(max(user,old[0]),max(system,old[1]));mem={k:int(v)*1024 for k,v in re.findall(r'^(VmRSS|VmSize|VmPeak):\s*(\d+) kB$',status,re.M)};smaps=(base/'smaps_rollup').read_text();match=re.search(r'^Pss:\s*(\d+) kB$',smaps,re.M);pv=int(match[1])*1024 if match else 0;details.append(dict(pid=pid,start_token=pid_token,user_cpu_seconds=user,system_cpu_seconds=system,pss_bytes=pv,**mem));rss+=mem.get('VmRSS',0);pss+=pv;virtual+=mem.get('VmSize',0)
    except(FileNotFoundError,ProcessLookupError,PermissionError):pass
   elapsed=time.monotonic()-started
   if elapsed-last_disk>=10:
    latest_disk=disk(paths);last_disk=elapsed
    for key in maxdisk:maxdisk[key]=max(maxdisk[key],latest_disk[key])
   for key,value in [('rss_bytes',rss),('pss_bytes',pss),('virtual_bytes',virtual)]:peaks[key]=max(peaks[key],value)
   sample=dict(seconds=elapsed,summed_rss_bytes=rss,proportional_set_size_bytes=pss,summed_virtual_size_bytes=virtual,observed_user_cpu_seconds=sum(v[0]for v in seen_cpu.values()),observed_system_cpu_seconds=sum(v[1]for v in seen_cpu.values()),disk=latest_disk,processes=details);stream.write(json.dumps(sample,separators=(',',':'))+'\n');stream.flush();count+=1
   if not ready.exists():
    temp=ready.with_suffix('.pending');temp.write_text(json.dumps(dict(status='OBSERVER_READY_BEFORE_CHILD_DISPATCH',pid=a.pid,start_token=token,first_sample_seconds=elapsed,observer_pid=os.getpid()))+'\n');temp.replace(ready)
   if stop.exists():reason='EXPLICIT_STOP_AFTER_CONTROLLER_EXIT';break
   time.sleep(a.interval)
 finaldisk=disk(paths)
 for key in maxdisk:maxdisk[key]=max(maxdisk[key],finaldisk[key])
 result=dict(status='COMPLETED_INDEPENDENT_PROCESS_TREE_SAMPLING_NOT_PROOF_ACCEPTANCE',termination=reason,pid=a.pid,parent_start_token=token,seconds=time.monotonic()-started,samples=count,interval_seconds=a.interval,sampled_peak_summed_rss_bytes=peaks['rss_bytes'],sampled_peak_pss_bytes=peaks['pss_bytes'],sampled_peak_virtual_bytes=peaks['virtual_bytes'],observed_user_cpu_seconds=sum(v[0]for v in seen_cpu.values()),observed_system_cpu_seconds=sum(v[1]for v in seen_cpu.values()),disk_peaks=maxdisk,disk_final=finaldisk,paths=list(map(str,paths)),samples_sha256=hashlib.sha256((out/'samples.jsonl').read_bytes()).hexdigest(),qualification='Sampled aggregate peaks may miss between-sample maxima; observed per-PID CPU is a sampled lower bound for short-lived processes. GNU time records complete per-compiler CPU/peakRSS separately. RSS double-counts shared mappings; PSS apportions them. Observer READY precedes the controller child launch.',timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat());temp=out/'RESULT.json.pending';temp.write_text(json.dumps(result,indent=2)+'\n');temp.replace(out/'RESULT.json');print(json.dumps({k:result[k]for k in ['status','seconds','samples','sampled_peak_summed_rss_bytes','sampled_peak_pss_bytes']}))
if __name__=='__main__':main()
