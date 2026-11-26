#!/usr/bin/env python3
# Copyright (c) 2026 IEANTN contributors. All rights reserved.
# Released under Apache 2.0 license as described in LICENSE.
# Authors: OpenAI (Codex)
"""Fresh physical runs of the unchanged C source used by the full-CMS proof.
This records physical observations under the disclosed platform contracts; it is
not a replacement for source/AST/execution correctness in reproduce_dual.py.
"""
import argparse,os,platform,shutil,subprocess,sys,time
from pathlib import Path
from reproduce_dual import need,publish,sha

def main():
 a=argparse.ArgumentParser(allow_abbrev=False);a.add_argument('--repository',type=Path,required=True);a.add_argument('--run',type=Path,required=True);o=a.parse_args();need(not os.path.lexists(o.run),'Fresh destination required')
 src=o.repository.resolve(strict=True)/'Solutions/RH080Study.v1/pv/dual_grid.c';need(sha(src)=='da11ed48a9596134df48f29066299b39c458ac891daa90b9380dcca469ea7feb','Source differs from the verified C bytes')
 gcc=Path(shutil.which('gcc')).resolve(strict=True);version=subprocess.check_output([str(gcc),'--version'],text=True);need('11.4.0'in version.splitlines()[0],'Pinned GCC11.4.0 required');o.run.mkdir(parents=True)
 plan={'status':'FROZEN_PHYSICAL_C_RUN_PLAN_NOT_PLATFORM_CORRECTNESS_PROOF','source_sha256':sha(src),'controller_sha256':sha(Path(__file__)),'compiler_sha256':sha(gcc),'compiler_version':version,'machine':platform.uname()._asdict(),'python':sys.version,'optimization':sys.flags.optimize,'word_bytes':8,'stdout_reference':'1221161\n','command':sys.argv};publish(o.run/'PLAN.json',plan);rows=[]
 for name,flags in [('O0',['-O0']),('O2',['-O2']),('O3',['-O3']),('UBSan',['-O2','-fsanitize=undefined','-fno-sanitize-recover=all'])]:
  exe=o.run/name;cmd=[str(gcc),'-std=c11','-Wall','-Wextra','-Werror',*flags,str(src),'-o',str(exe)];t=time.monotonic();b=subprocess.run(cmd,capture_output=True);need(b.returncode==0,'Compilation failed '+name)
  run=subprocess.run([str(exe)],capture_output=True);need(run.returncode==0 and run.stdout==b'1221161\n'and not run.stderr,'Observed source execution mismatch '+name)
  (o.run/(name+'.stdout')).write_bytes(run.stdout);rows.append({'case':name,'command':cmd,'seconds':time.monotonic()-t,'binary_sha256':sha(exe),'stdout_sha256':sha(o.run/(name+'.stdout')),'returncode':run.returncode})
 need(sha(src)==plan['source_sha256']and sha(Path(__file__))==plan['controller_sha256'],'Source changed during physical runs')
 publish(o.run/'RESULT.json',{'status':'PASS_4_FRESH_PHYSICAL_C_EXECUTIONS','rows':rows,'plan_source_sha256':plan['source_sha256'],'platform_boundary':'Trust exact generic C compiler/uint64 ABI, documented printf success, OS and hardware. The Lean model and source correspondence are separately rebuilt from source; no physical trace formalization claimed.'});print('PASS_4_FRESH_PHYSICAL_C_EXECUTIONS')
if __name__=='__main__':main()
