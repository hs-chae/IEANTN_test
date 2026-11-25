#!/usr/bin/env python3
"""External descendant-RSS monitor including children of every Linux task.

Samples start when this monitor starts; the summary never labels that window
as coverage of the complete earlier run or as an exact physical-memory peak.
"""
import argparse, datetime, hashlib, json, time
from pathlib import Path

def rss_tree(root):
    todo=[root];seen=set();rss=0;lean=[]
    while todo:
        pid=todo.pop()
        if pid in seen:continue
        seen.add(pid);proc=Path('/proc')/str(pid)
        try:
            rss+=sum(int(line.split()[1])*1024 for line in (proc/'status').read_text().splitlines() if line.startswith('VmRSS:'))
            args=(proc/'cmdline').read_bytes().decode().split('\0')
            if args and args[0].endswith('/lean'):lean.append(pid)
            for task in (proc/'task').iterdir():
                try:todo.extend(int(value) for value in (task/'children').read_text().split())
                except OSError:pass
        except (OSError,UnicodeError):pass
    return rss,sorted(lean),len(seen)
def available():return int(next(line.split()[1] for line in Path('/proc/meminfo').read_text().splitlines() if line.startswith('MemAvailable:')))*1024
def main():
    parser=argparse.ArgumentParser(allow_abbrev=False);parser.add_argument('--pid',type=int,required=True);parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args()
    if args.out.exists():raise RuntimeError('Fresh monitor directory required')
    proc=Path('/proc')/str(args.pid);identity=(proc/'cmdline').read_bytes();args.out.mkdir(parents=True)
    started=datetime.datetime.now(datetime.timezone.utc).isoformat();start=time.monotonic();samples=[]
    with (args.out/'samples.jsonl').open('w') as log:
        while True:
            try:
                if (proc/'cmdline').read_bytes()!=identity:break
            except OSError:break
            rss,lean,count=rss_tree(args.pid)
            sample=dict(seconds=time.monotonic()-start,RSS_sum_bytes=rss,Lean_PIDs=lean,process_count=count,host_MemAvailable_bytes=available());samples.append(sample)
            log.write(json.dumps(sample)+'\n');log.flush()
            if len(samples)%20==0:(args.out/'LIVE.json').write_text(json.dumps(sample)+'\n')
            time.sleep(0.5)
    result=dict(status='COMPLETE_PARTIAL_WINDOW_DESCENDANT_RSS_SAMPLING',root_pid=args.pid,root_cmdline_sha256=hashlib.sha256(identity).hexdigest(),monitor_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),started_utc=started,seconds=time.monotonic()-start,interval_seconds=0.5,samples=len(samples),maximum_sampled_descendant_RSS_bytes=max((s['RSS_sum_bytes'] for s in samples),default=0),maximum_observed_Lean_workers=max((len(s['Lean_PIDs']) for s in samples),default=0),minimum_sampled_host_MemAvailable_bytes=min((s['host_MemAvailable_bytes'] for s in samples),default=0),coverage='Onlythismonitorwindow;startedaftercoldrunadmission. SumofprocessRSSmaysharedoublecountpages;notexactphysicalpeak.')
    (args.out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
if __name__=='__main__':main()
