#!/usr/bin/env python3
"""Rebuild all673 selected analytic application modules from unchanged sources.
Only the exact pinned generic libraries are reused. Numerical Taylor leaves
are regenerated inside the kernel proofs; no native numerical output is used.
"""
from pathlib import Path
import argparse,subprocess,sys
from reproduce_profiled_closure import strict_json,need,sha
S=Path(__file__).resolve().parents[1];NETWORK=S.parents[1]
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--context',type=Path,default=S/'BUILD_CONTEXT.json');p.add_argument('--out',type=Path,required=True);p.add_argument('--jobs',type=int,default=4);p.add_argument('--cpus',default='8,9,10,11');p.add_argument('--memory-gib',type=int,default=48);p.add_argument('--aggregate-gib',type=int,default=192);p.add_argument('--host-reserve-gib',type=int,default=512);p.add_argument('--plan-only',action='store_true');a=p.parse_args();lock=strict_json(S/'evidence/coupled-analytic-1250-v1/SOURCE_LOCK.json');need(lock['schema']=='ieantn.coupled-analytic-source-closure.v1'and lock['module_count']==len(lock['modules'])==673,'entire locked analytic closure');need(len({m['module']for m in lock['modules']})==673,'unique compiler identities')
 for module in lock['modules']:
  source=(NETWORK/module['network_relative_source']).resolve();need(source.is_relative_to(NETWORK)and sha(source)==module['source_sha256'],'current exact scientific source '+module['module'])
 need(sha(S/'scripts/reproduce_guarded_coupled_closure.py')==lock['guarded_driver_sha256'],'exact guarded resource and acceptance helper')
 modes=['-OO']if sys.flags.optimize>=2 else['-O']if sys.flags.optimize else[];command=[sys.executable,*modes,str(S/'scripts/reproduce_guarded_coupled_closure.py'),'--context',str(a.context.resolve()),'--out',str(a.out.resolve()),'--jobs',str(a.jobs),'--cpus',a.cpus,'--memory-gib',str(a.memory_gib),'--aggregate-gib',str(a.aggregate_gib),'--host-reserve-gib',str(a.host_reserve_gib)]
 for root in lock['roots']:command+=['--root',root]
 for theorem in lock['theorems']:command+=['--theorem',theorem]
 for relative in lock['source_roots']:
  root=(NETWORK/relative).resolve()
  if root not in[S,NETWORK]:command+=['--application-source-root',str(root)]
 if a.plan_only:command+=['--plan-only']
 code=subprocess.call(command);need(code==0,'complete replay/plan must pass')
 if not a.plan_only:
  need(subprocess.call([sys.executable,*modes,str(S/'scripts/reproduce_guarded_coupled_closure.py'),'--check',str(a.out.resolve())])==0,'independent complete source/object/log/axiom readback')
if __name__=='__main__':main()
