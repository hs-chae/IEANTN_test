#!/usr/bin/env python3
"""Observe one owned process tree; explicit stop handshake finishes before parent exit."""
from pathlib import Path
import argparse,datetime,hashlib,json,os,re,subprocess,time
from monitor_demand_resources import disk,identity,need
S=Path(__file__).resolve().parents[1]
def main():
    p=argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--pid',type=int,required=True);p.add_argument('--path',type=Path,action='append',required=True)
    p.add_argument('--out',type=Path,required=True);p.add_argument('--stop-file',type=Path,required=True)
    p.add_argument('--interval',type=float,default=1.0);a=p.parse_args()
    context=json.loads((S/'BUILD_CONTEXT.json').read_text());owned_root=Path(context['new_application_object_root']).resolve().parent
    paths=[v.resolve()for v in a.path];stop=a.stop_file.resolve();out=a.out.resolve()
    need(0.1<=a.interval<=10,'bounded sampling interval');need(out.is_relative_to(owned_root)and not out.exists()and stop.is_relative_to(owned_root)and not stop.exists(),'fresh experiment-owned observer paths')
    need(all(v.is_relative_to(owned_root)for v in paths),'experiment-owned measured paths')
    token=identity(a.pid);need(token is not None,'actual live fixed parent');out.mkdir(parents=True)
    started=time.monotonic();maximum_rss=maximum_pss=maximum_virtual=maximum_compiler_vmpeak=0;count=0;disk_at=-20;latest_disk={};maxdisk=dict(logical_bytes=0,allocated_bytes=0,files=0);reason='PARENT_EXIT'
    with(out/'samples.jsonl').open('x')as output:
        while identity(a.pid)==token:
            rows=[tuple(map(int,line.split()))for line in subprocess.check_output(['ps','-eo','pid=,ppid='],text=True).splitlines()];tree={a.pid}
            while True:
                expanded=tree|{pid for pid,ppid in rows if ppid in tree}
                if expanded==tree:break
                tree=expanded
            details=[];rss=pss=virtual=0
            for pid in sorted(tree):
                try:
                    fields={key:int(value)*1024 for key,value in re.findall(r'^(VmRSS|VmSize|VmPeak):\s*(\d+) kB$',Path('/proc',str(pid),'status').read_text(),re.M)}
                    smaps=Path('/proc',str(pid),'smaps_rollup').read_text();pss_match=re.search(r'^Pss:\s*(\d+) kB$',smaps,re.M);pv=int(pss_match[1])*1024 if pss_match else 0
                    exe=str(Path('/proc',str(pid),'exe').resolve());entry=dict(pid=pid,start_identity=identity(pid),executable=exe,**fields,pss_bytes=pv);details.append(entry)
                    rss+=fields.get('VmRSS',0);pss+=pv;virtual+=fields.get('VmSize',0)
                    if exe==context['compiler']:maximum_compiler_vmpeak=max(maximum_compiler_vmpeak,fields.get('VmPeak',0))
                except(FileNotFoundError,ProcessLookupError,PermissionError):pass
            elapsed=time.monotonic()-started;maximum_rss=max(maximum_rss,rss);maximum_pss=max(maximum_pss,pss);maximum_virtual=max(maximum_virtual,virtual)
            if elapsed-disk_at>=10:
                latest_disk=disk(paths);disk_at=elapsed
                for key in maxdisk:maxdisk[key]=max(maxdisk[key],latest_disk[key])
            sample=dict(seconds=elapsed,summed_rss_bytes=rss,proportional_set_size_bytes=pss,summed_virtual_size_bytes=virtual,compiler_observed_vmpeak_bytes=maximum_compiler_vmpeak,disk=latest_disk,processes=details)
            output.write(json.dumps(sample,separators=(',',':'))+'\n');output.flush();count+=1
            if stop.exists():reason='EXPLICIT_PARENT_STOP_HANDSHAKE';break
            time.sleep(a.interval)
    finaldisk=disk(paths)
    for key in maxdisk:maxdisk[key]=max(maxdisk[key],finaldisk[key])
    result=dict(status='COMPLETED_PROCESS_TREE_VIRTUAL_SAMPLING_NOT_VERIFICATION',termination=reason,pid=a.pid,parent_start_identity=token,seconds=time.monotonic()-started,samples=count,interval_seconds=a.interval,sampled_peak_summed_rss_bytes=maximum_rss,sampled_peak_proportional_set_size_bytes=maximum_pss,sampled_peak_summed_virtual_size_bytes=maximum_virtual,compiler_observed_vmpeak_bytes=maximum_compiler_vmpeak,disk_peaks=maxdisk,disk_final=finaldisk,paths=list(map(str,paths)),samples_sha256=hashlib.sha256((out/'samples.jsonl').read_bytes()).hexdigest(),qualification='Observed /proc VmPeak maxima are sampled per-compiler virtual-address-space high-water marks, distinct from physical RAM. GNU time independently supplies complete per-compiler peak RSS. RSS sums shared mappings; PSS apportions them. Explicit stop handshake permits final receipt while parent remains live.',timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat())
    stage=out/'RESULT.json.pending';stage.write_text(json.dumps(result,indent=2)+'\n');stage.replace(out/'RESULT.json');print(json.dumps(result))
if __name__=='__main__':main()
