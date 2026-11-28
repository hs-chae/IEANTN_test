#!/usr/bin/env python3
"""Minimal actual deadline controls only; no renaming workload or math compiler."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,subprocess,sys

def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--source',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();need(not a.out.exists(),'Fresh timeout-control output required');a.out.mkdir()
 spec=importlib.util.spec_from_file_location('guard',a.source);g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g);old=g.original();before=old.cgroup();need(before.get('memory.max')==str(300*2**30)and before.get('memory.swap.max')=='0','Owned300GiB/noSwap control service required');records=[]
 for mode,opt in [('normal',[]),('O',['-O']),('OO',['-OO'])]:
  for label,extra,duration,good in [('default',[],'.1',True),('max7200',['--deadline-seconds','7200'],'.1',True),('actual-timeout',['--deadline-seconds','1'],'20',False)]:
   root=a.out/(mode+'-'+label);root.mkdir();work=root/'workspace';work.mkdir();receipt=root/'RESOURCE.json';plan=root/'COMMAND.json';child=[sys.executable,'-c','import time;time.sleep('+duration+')'];old.publish(plan,dict(command=child,source_pins=[dict(path=str(a.source),sha256=sha(a.source))]));cmd=[sys.executable]+opt+[str(a.source),'--root',str(root),'--workspace',str(work),'--command',str(plan),'--receipt',str(receipt),'--live',str(root/'LIVE.json'),'--workspace-limit-gib','12','--initial-scratch-limit-gib','280','--sample-seconds','1']+extra;r=subprocess.run(cmd,capture_output=True,text=True,timeout=15);(root/'stdout').write_text(r.stdout);(root/'stderr').write_text(r.stderr);need((r.returncode==0)==good,'Unexpected actual deadline outcome');result=g.read(receipt)
   if good:need(result['status']=='COMPLETE_CHILD_NOT_MATHEMATICAL_ACCEPTANCE'and result['returncode']==0 and result['failure']is None,'Positive deadline child incomplete')
   else:
    need(result['status']=='INCOMPLETE_NO_BOOTSTRAP_RESOURCE_ACCEPTANCE'and 'wall deadline reached'in(result['failure']or''),'Actual wall deadline not enforced')
    for sample in result['paused_scan_observations']:
     for prior in sample['stable_stopped']:
      current=g.process(prior['PID'],prior['cgroup']);need(current is None or g.identity(current)!=g.identity(prior)or current['state']in ['Z','X'],'Timed-out owned child remained live/stopped')
   records.append(dict(mode=mode,case=label,command=cmd,returncode=r.returncode,resource_receipt_sha256=sha(receipt)))
 old.publish(a.out/'RESULT.json',dict(status='PASS_ACTUAL_GENERIC_V4_DEFAULT_MAX_AND_TIMEOUT_ALL_MODES',positive=6,actual_timeout_negative=3,records=records,source_sha256=sha(a.source),controller_sha256=sha(Path(__file__)),unchanged_renaming_mechanism_not_rerun=True,no_math_or_PV_claim=True));print('PASS6positive/3actualtimeouts all3modes; no renaming or math')
if __name__=='__main__':main()
