#!/usr/bin/env python3
"""Sample a fixed controller's process tree and experiment-owned artifact paths."""
from pathlib import Path
import argparse,datetime,hashlib,json,os,subprocess,time
OWN=Path('/data/ivy-ramanujan-source-pv-20261119')
def need(v,m):
    if not v:raise ValueError(m)
def identity(pid):
    try:return Path('/proc',str(pid),'stat').read_text().rsplit(')',1)[1].split()[19]
    except(FileNotFoundError,ProcessLookupError):return None
def disk(paths):
    seen=set();logical=allocated=0;files=0
    for root in paths:
        for base,dirs,names in os.walk(root):
            for name in names:
                path=Path(base)/name
                if path.is_symlink():continue
                try:s=path.stat()
                except FileNotFoundError:continue
                key=(s.st_dev,s.st_ino)
                if key in seen:continue
                seen.add(key);files+=1;logical+=s.st_size;allocated+=s.st_blocks*512
    return dict(logical_bytes=logical,allocated_bytes=allocated,files=files)
def main():
    p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--pid',type=int,required=True);p.add_argument('--path',type=Path,action='append',required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
    need(a.out.resolve().is_relative_to(OWN)and not a.out.exists(),'fresh owned output');paths=[p.resolve()for p in a.path];need(all(p.is_relative_to(OWN)for p in paths),'only experiment-owned paths')
    token=identity(a.pid);need(token is not None,'actual live controller');a.out.mkdir(parents=True);start=time.monotonic();maximum_rss=maximum_pss=0;maximum_disk={'logical_bytes':0,'allocated_bytes':0,'files':0};samples=0;disk_at=-20;latest_disk={}
    with(a.out/'samples.jsonl').open('x')as f:
        while identity(a.pid)==token:
            result=subprocess.run(['ps','-eo','pid=,ppid=,rss='],capture_output=True,text=True,check=True);rows=[tuple(map(int,l.split()))for l in result.stdout.splitlines()];owned={a.pid}
            while True:
                expanded=owned|{pid for pid,ppid,rss in rows if ppid in owned}
                if expanded==owned:break
                owned=expanded
            rss=sum(rss*1024 for pid,ppid,rss in rows if pid in owned);pss=0;pss_read=0
            for pid in owned:
                try:
                    text=Path('/proc',str(pid),'smaps_rollup').read_text()
                    for line in text.splitlines():
                        if line.startswith('Pss:'):pss+=int(line.split()[1])*1024;pss_read+=1
                except(FileNotFoundError,ProcessLookupError,PermissionError):pass
            maximum_rss=max(maximum_rss,rss);maximum_pss=max(maximum_pss,pss);elapsed=time.monotonic()-start
            if elapsed-disk_at>=10:
                latest_disk=disk(paths);disk_at=elapsed
                for k in maximum_disk:maximum_disk[k]=max(maximum_disk[k],latest_disk[k])
            sample=dict(seconds=elapsed,processes=len(owned),summed_rss_bytes=rss,proportional_set_size_bytes=pss,pss_processes_read=pss_read,disk=latest_disk)
            f.write(json.dumps(sample,separators=(',',':'))+'\n');f.flush();samples+=1;time.sleep(1)
    final_disk=disk(paths)
    for k in maximum_disk:maximum_disk[k]=max(maximum_disk[k],final_disk[k])
    result=dict(status='COMPLETED_PROCESS_TREE_SAMPLING_NOT_VERIFICATION',pid=a.pid,process_start_identity=token,seconds=time.monotonic()-start,samples=samples,sampled_peak_summed_rss_bytes=maximum_rss,sampled_peak_proportional_set_size_bytes=maximum_pss,disk_peaks=maximum_disk,disk_final=final_disk,paths=list(map(str,paths)),qualification='Sampled one-second peaks; RSS sums shared mappings, PSS apportions them. Compiler per-attempt /usr/bin/time receipts independently record exact process peak RSS. Sampling begins after controller launch and does not claim an earlier unsampled peak.',samples_sha256=hashlib.sha256((a.out/'samples.jsonl').read_bytes()).hexdigest(),timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat())
    tmp=a.out/'RESULT.json.pending';tmp.write_text(json.dumps(result,indent=2)+'\n');tmp.replace(a.out/'RESULT.json');print(json.dumps(result))
if __name__=='__main__':main()
